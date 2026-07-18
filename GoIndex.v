(** * GoIndex — the production occurrence index over the ONE raw [GoProgram] (Source Forest campaign, C2).

    [GoIndex] derives, from one exact immutable [GoProgram] snapshot, a canonical file-local occurrence
    identity for every currently-represented semantic source occurrence, a certified structural index over
    the ORIGINAL source forest, snapshot-indexed validated references, total navigation, and an indexed
    traversal that supplies the original syntax fragment and its canonical reference together.  It is
    STRUCTURAL and SOURCE-derived: it imports only [GoAST] (the one source AST), [Collections] (the standard
    map foundation), and [FilePath]; it does NOT know semantic types, compiler acceptance, rendering, or
    diagnostics (it must not import [GoTypes]/[GoCompile]/[GoSafe]/[GoRender]/[GoEmit]).  It preserves and
    GENERALIZES the accepted C0/C0A/C0B occurrence-index spike ([OccurrenceSpike]) to the real grammar.

    COLLECTION LAW (CLAUDE.md rule 10 / ARCHITECTURE.md): the per-file local-node table is the STANDARD
    pinned-stdlib positive-key map [FMapPositive.PositiveMap] (aliased [Collections.NodeMapBase]); the outer
    program index is the STANDARD [FMapAVL] file map ([Collections.FileMapBase]) keyed by [FilePath].  Fido
    authors NO collection storage or generic collection algorithm; the thin sealed [NodeTable] wrapper stores
    a [Collections.NodeMapBase] and proves its three laws directly from the standard map facts.  C2 RETAINS
    these selected standard maps (the sealing hides the map CONSTRUCTORS and RAW operations, NOT the choice of
    collection).

    ---- MILESTONE STATE (C2 in progress) ---------------------------------------------------------------
    This module is being grown bottom-up in fully-proven, always-green steps.  Present now: the sealed node
    table, the current occurrence universe (kinds/roles/metadata), the one-pass per-file index builder over
    the real [GoAST] grammar (file root, package clause, declarations, statements, println arguments, and
    unary conversion operands), the INDEPENDENT table-free source-occurrence specification, and the
    load-bearing UNIVERSAL per-file source/index exactness theorem.  Still to land before the C2 ROOT
    barrier: the structural navigation invariants (parent / interval-jump children / ancestry), the
    snapshot-indexed sealed reference layer over [GoProgram], the total query API, the canonical enumeration,
    and the mutation-sensitive / snapshot-locality fixtures. *)

From Stdlib Require Import PArith List Bool Lia Sorted Recdef Wf_nat Arith.
From Fido Require Import FilePath Collections GoAST.
Import ListNotations.
Local Open Scope positive_scope.

(* ================================================================================================= *)
(** ** The SELECTED node table: an ABSTRACT interface, implemented internally by the STANDARD pinned-stdlib *)
(*    positive-key map [Collections.NodeMapBase] ([FMapPositive]).  Callers see ONLY                       *)
(*    [NodeTable.table]/[empty]/[get]/[set] and the three laws; the sealing hides the standard map's        *)
(*    CONSTRUCTORS and RAW operations, NOT the choice of collection. *)
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
(** ** Occurrence kinds, roles, and metadata (directive §4/§5).                                       *)
(* ================================================================================================= *)

(* The current occurrence universe: file root, package clause, top-level declaration, statement, expression.
   No kind for unsupported future syntax (no import/name/type kind ahead of its syntax). *)
Inductive SyntaxKind := KFile | KPackageClause | KTopLevelDecl | KStatement | KExpression.

(* How an occurrence participates in its parent (directive §5).  One role suffices for every conversion
   operand — integer/float/complex conversions share the SAME structural child relationship. *)
Inductive NodeRole :=
| RFileRoot                  (* the file root itself *)
| RFilePackage               (* the file's package clause *)
| RFileDecl (n : nat)        (* the n-th top-level declaration of a file *)
| RDeclStmt (n : nat)        (* the n-th statement in a declaration body *)
| RPrintlnArg (n : nat)      (* the n-th argument of a println statement *)
| RConversionOperand.        (* the single operand of an explicit conversion expression *)

(* Small structural metadata; NO copy of the recursive subtree (directive §5 / §23.12). *)
Record NodeMeta := mkMeta {
  nm_kind        : SyntaxKind;
  nm_parent      : option positive;   (* file-local parent id; None only for a file root *)
  nm_role        : NodeRole;
  nm_subtree_end : positive           (* last preorder id in this occurrence's subtree *)
}.

Definition root_id : positive := 1.       (* every file root's canonical local id (directive §4.1) *)
Definition pkg_id  : positive := 2.       (* the package clause is the file root's first child = Pos.succ root_id *)

(* total extraction from a provably-present option — the key to a total validated-reference API (used by the
   reference layer that follows this milestone). *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* [ImportSpecSyntax] is EMPTY, so any [list ImportSpecSyntax] is intrinsically [nil]; the builder and the
   source spec STRUCTURALLY consume [source_imports] (directive §4.3) so a future import constructor forces
   this definition and its proofs to change rather than being silently ignored. *)
Lemma import_list_nil : forall (l : list ImportSpecSyntax), l = [].
Proof. intros [|i rest]; [ reflexivity | destruct i ]. Qed.

(* ================================================================================================= *)
(** ** The one-pass per-file index builder (directive §7).                                             *)
(*    Each builder threads a fresh-id counter and inserts each occurrence's metadata EXACTLY ONCE via  *)
(*    one standard-map [NodeTable.set]; it never searches, compares, or copies syntax subtrees.  A      *)
(*    subtree builder returns the subtree's last id ([se], its [subtree_end]); a sibling-sequence       *)
(*    builder returns the next free id.  Meta for an internal node is inserted AFTER its children so     *)
(*    [subtree_end] is known.  Expression leaves have no child; an explicit conversion has exactly one   *)
(*    operand child (role [RConversionOperand]). *)
(* ================================================================================================= *)

Fixpoint build_expr (parent : positive) (role : NodeRole) (me : positive) (e : GoExpr)
                    (t : NodeTable.table NodeMeta) : NodeTable.table NodeMeta * positive (* subtree_end *) :=
  match e with
  | EBool _ | EInt _ | ENeg _ | EString _ | EFloat _ | EComplex _ =>
      (NodeTable.set me (mkMeta KExpression (Some parent) role me) t, me)
  | EIntConvert _ x =>
      let '(t1, e1) := build_expr me RConversionOperand (Pos.succ me) x t in
      (NodeTable.set me (mkMeta KExpression (Some parent) role e1) t1, e1)
  | EFloatConvert _ x =>
      let '(t1, e1) := build_expr me RConversionOperand (Pos.succ me) x t in
      (NodeTable.set me (mkMeta KExpression (Some parent) role e1) t1, e1)
  | EComplexConvert _ x =>
      let '(t1, e1) := build_expr me RConversionOperand (Pos.succ me) x t in
      (NodeTable.set me (mkMeta KExpression (Some parent) role e1) t1, e1)
  end.

(* one println argument: an expression subtree carrying its argument role. *)
Definition build_arg (parent : positive) (aidx : nat) (me : positive) (e : GoExpr)
                     (t : NodeTable.table NodeMeta) : NodeTable.table NodeMeta * positive :=
  build_expr parent (RPrintlnArg aidx) me e t.

(* A generic left-to-right sibling-sequence builder: builds each element as a subtree rooted at the running
   fresh id and advances.  Returns the next free id.  [bx] is the per-element subtree builder. *)
Fixpoint build_seq {X} (bx : positive -> nat -> positive -> X -> NodeTable.table NodeMeta -> NodeTable.table NodeMeta * positive)
                   (parent : positive) (i0 : nat) (me0 : positive) (xs : list X) (t : NodeTable.table NodeMeta)
  : NodeTable.table NodeMeta * positive (* next free id *) :=
  match xs with
  | []        => (t, me0)
  | x :: rest =>
      let '(t1, se) := bx parent i0 me0 x t in
      build_seq bx parent (S i0) (Pos.succ se) rest t1
  end.

(* a statement wraps a left-to-right run of println-argument subtrees. *)
Definition build_stmt (parent : positive) (sidx : nat) (me : positive) (s : GoStmt)
                      (t : NodeTable.table NodeMeta) : NodeTable.table NodeMeta * positive :=
  match s with
  | SPrintln args =>
      let '(t1, nx) := build_seq build_arg me 0 (Pos.succ me) args t in
      (NodeTable.set me (mkMeta KStatement (Some parent) (RDeclStmt sidx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

(* a declaration wraps a left-to-right run of statement subtrees. *)
Definition build_decl (parent : positive) (didx : nat) (me : positive) (d : GoDecl)
                      (t : NodeTable.table NodeMeta) : NodeTable.table NodeMeta * positive :=
  match d with
  | DMain body =>
      let '(t1, nx) := build_seq build_stmt me 0 (Pos.succ me) body t in
      (NodeTable.set me (mkMeta KTopLevelDecl (Some parent) (RFileDecl didx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

(* The per-file index carries NO path (the path is the outer map key — no second file identity). *)
Record FileIndex := mkFI {
  fi_table : NodeTable.table NodeMeta;
  fi_count : positive           (* number of occurrences = last local id; ids are [1 .. fi_count] *)
}.

(* The file root's children in canonical preorder are the package clause (id [pkg_id] = 2) then the
   declarations (from id 3).  [source_imports] is STRUCTURALLY consumed (directive §4.3): it is intrinsically
   [nil] today, so no import occurrence exists; a future import constructor makes the [i :: _] branch
   constructible and forces this definition and its proofs to change. *)
Definition build_file (f : GoSourceFile) : FileIndex :=
  match source_imports f with
  | i :: _ => match i with end
  | [] =>
      let tp := NodeTable.set pkg_id (mkMeta KPackageClause (Some root_id) RFilePackage pkg_id) NodeTable.empty in
      let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ pkg_id) (source_decls f) tp in
      let cnt := Pos.pred nx in
      mkFI (NodeTable.set root_id (mkMeta KFile None RFileRoot cnt) t1) cnt
  end.

(* ================================================================================================= *)
(** ** Boundary functions: the last preorder id of a subtree / the next free id after a sibling run.   *)
(*    These are TABLE-FREE — derived purely from source structure — and shared by the builder-agnostic  *)
(*    source-occurrence specification below.                                                            *)
(* ================================================================================================= *)

Fixpoint end_expr (me : positive) (e : GoExpr) : positive :=
  match e with
  | EBool _ | EInt _ | ENeg _ | EString _ | EFloat _ | EComplex _ => me
  | EIntConvert _ x => end_expr (Pos.succ me) x
  | EFloatConvert _ x => end_expr (Pos.succ me) x
  | EComplexConvert _ x => end_expr (Pos.succ me) x
  end.
Fixpoint next_exprs (me : positive) (es : list GoExpr) : positive :=
  match es with [] => me | e :: rest => next_exprs (Pos.succ (end_expr me e)) rest end.
Definition end_stmt (me : positive) (s : GoStmt) : positive :=
  match s with SPrintln args => Pos.pred (next_exprs (Pos.succ me) args) end.
Fixpoint next_stmts (me : positive) (ss : list GoStmt) : positive :=
  match ss with [] => me | s :: rest => next_stmts (Pos.succ (end_stmt me s)) rest end.
Definition end_decl (me : positive) (d : GoDecl) : positive :=
  match d with DMain body => Pos.pred (next_stmts (Pos.succ me) body) end.
Fixpoint next_decls (me : positive) (ds : list GoDecl) : positive :=
  match ds with [] => me | d :: rest => next_decls (Pos.succ (end_decl me d)) rest end.
Definition count_file (f : GoSourceFile) : positive := Pos.pred (next_decls (Pos.succ pkg_id) (source_decls f)).

(* --- the builder's returned subtree-end / next-free-id agree with the table-free boundary functions. --- *)

Lemma build_expr_end : forall e parent role me t, snd (build_expr parent role me e t) = end_expr me e.
Proof.
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent role me t; try reflexivity;
    (cbn [build_expr end_expr]; specialize (IHx me RConversionOperand (Pos.succ me) t);
     destruct (build_expr me RConversionOperand (Pos.succ me) x t) as [t1 e1]; cbn [snd] in IHx |- *;
     rewrite IHx; reflexivity).
Qed.

Lemma build_arg_end : forall e parent aidx me t, snd (build_arg parent aidx me e t) = end_expr me e.
Proof. intros. apply build_expr_end. Qed.

Lemma build_seq_arg_next : forall args parent i me t,
  snd (build_seq build_arg parent i me args t) = next_exprs me args.
Proof.
  induction args as [|e rest IH]; intros parent i me t; [reflexivity|].
  simpl. rewrite <- (build_arg_end e parent i me t).
  destruct (build_arg parent i me e t) as [t1 se]. simpl. apply IH.
Qed.

Lemma build_stmt_end : forall s parent i me t, snd (build_stmt parent i me s t) = end_stmt me s.
Proof.
  intros [args] parent i me t. cbn [build_stmt end_stmt].
  rewrite <- (build_seq_arg_next args me 0 (Pos.succ me) t).
  destruct (build_seq build_arg me 0 (Pos.succ me) args t) as [t1 nx]. reflexivity.
Qed.

Lemma build_seq_stmt_next : forall ss parent i me t,
  snd (build_seq build_stmt parent i me ss t) = next_stmts me ss.
Proof.
  induction ss as [|s rest IH]; intros parent i me t; [reflexivity|].
  simpl. rewrite <- (build_stmt_end s parent i me t).
  destruct (build_stmt parent i me s t) as [t1 se]. simpl. apply IH.
Qed.

Lemma build_decl_end : forall d parent i me t, snd (build_decl parent i me d t) = end_decl me d.
Proof.
  intros [body] parent i me t. cbn [build_decl end_decl].
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
  intros f. unfold build_file, count_file. destruct (source_imports f) as [|i ?]; [| destruct i].
  rewrite <- (build_seq_decl_next (source_decls f) root_id 0 (Pos.succ pkg_id)
                (NodeTable.set pkg_id (mkMeta KPackageClause (Some root_id) RFilePackage pkg_id) NodeTable.empty)).
  destruct (build_seq build_decl root_id 0 (Pos.succ pkg_id) (source_decls f)
              (NodeTable.set pkg_id (mkMeta KPackageClause (Some root_id) RFilePackage pkg_id) NodeTable.empty))
    as [t1 nx].
  reflexivity.
Qed.

(* ================================================================================================= *)
(** ** An INDEPENDENT source-occurrence specification (table-free, builder-independent) — directive §8.  *)
(*    For a source file and a local preorder id, this states — purely from the source syntax and the    *)
(*    boundary functions above — the EXACT occurrence that id designates and the metadata it SHOULD      *)
(*    carry.  It never consults [NodeTable], [build_*], or [FileIndex]; it is the semantic yardstick      *)
(*    against which [build_file] is proved correct in [build_file_source_exact].                         *)
(* ================================================================================================= *)

(* a kind-indexed view onto the ORIGINAL syntax fragment (no copied/parallel grammar). *)
Inductive SyntaxView : SyntaxKind -> Type :=
| ViewFile          : GoSourceFile -> SyntaxView KFile
| ViewPackageClause : PackageClauseSyntax -> SyntaxView KPackageClause
| ViewTopLevelDecl  : GoDecl -> SyntaxView KTopLevelDecl
| ViewStatement     : GoStmt -> SyntaxView KStatement
| ViewExpression    : GoExpr -> SyntaxView KExpression.

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
Definition view_expr (o : SourceOccurrence) : option GoExpr :=
  match occurrence_view o with ViewExpression e => Some e | _ => None end.

(* the occurrence a preorder id designates inside one expression subtree rooted at [me]. *)
Fixpoint occ_expr' (parent : positive) (role : NodeRole) (me : positive) (e : GoExpr) (target : positive)
  : option SourceOccurrence :=
  match e with
  | EBool _ | EInt _ | ENeg _ | EString _ | EFloat _ | EComplex _ =>
      if Pos.eqb target me then Some (mkOcc KExpression (ViewExpression e) (Some parent) role me) else None
  | EIntConvert _ x =>
      if Pos.eqb target me
      then Some (mkOcc KExpression (ViewExpression e) (Some parent) role (end_expr me e))
      else occ_expr' me RConversionOperand (Pos.succ me) x target
  | EFloatConvert _ x =>
      if Pos.eqb target me
      then Some (mkOcc KExpression (ViewExpression e) (Some parent) role (end_expr me e))
      else occ_expr' me RConversionOperand (Pos.succ me) x target
  | EComplexConvert _ x =>
      if Pos.eqb target me
      then Some (mkOcc KExpression (ViewExpression e) (Some parent) role (end_expr me e))
      else occ_expr' me RConversionOperand (Pos.succ me) x target
  end.
Fixpoint occ_exprs' (parent : positive) (aidx : nat) (me : positive) (es : list GoExpr) (target : positive)
  : option SourceOccurrence :=
  match es with
  | [] => None
  | e :: rest =>
      if Pos.leb target (end_expr me e)
      then occ_expr' parent (RPrintlnArg aidx) me e target
      else occ_exprs' parent (S aidx) (Pos.succ (end_expr me e)) rest target
  end.
Definition occ_stmt' (parent : positive) (sidx : nat) (me : positive) (s : GoStmt) (target : positive)
  : option SourceOccurrence :=
  match s with
  | SPrintln args =>
      if Pos.eqb target me
      then Some (mkOcc KStatement (ViewStatement s) (Some parent) (RDeclStmt sidx) (end_stmt me s))
      else occ_exprs' me 0 (Pos.succ me) args target
  end.
Fixpoint occ_stmts' (parent : positive) (sidx : nat) (me : positive) (ss : list GoStmt) (target : positive)
  : option SourceOccurrence :=
  match ss with
  | [] => None
  | s :: rest =>
      if Pos.leb target (end_stmt me s)
      then occ_stmt' parent sidx me s target
      else occ_stmts' parent (S sidx) (Pos.succ (end_stmt me s)) rest target
  end.
Definition occ_decl' (parent : positive) (didx : nat) (me : positive) (d : GoDecl) (target : positive)
  : option SourceOccurrence :=
  match d with
  | DMain body =>
      if Pos.eqb target me
      then Some (mkOcc KTopLevelDecl (ViewTopLevelDecl d) (Some parent) (RFileDecl didx) (end_decl me d))
      else occ_stmts' me 0 (Pos.succ me) body target
  end.
Fixpoint occ_decls' (parent : positive) (didx : nat) (me : positive) (ds : list GoDecl) (target : positive)
  : option SourceOccurrence :=
  match ds with
  | [] => None
  | d :: rest =>
      if Pos.leb target (end_decl me d)
      then occ_decl' parent didx me d target
      else occ_decls' parent (S didx) (Pos.succ (end_decl me d)) rest target
  end.
Definition source_occurrence_at (f : GoSourceFile) (target : positive) : option SourceOccurrence :=
  match source_imports f with
  | i :: _ => match i with end
  | [] =>
      if Pos.eqb target root_id
      then Some (mkOcc KFile (ViewFile f) None RFileRoot (count_file f))
      else if Pos.eqb target pkg_id
           then Some (mkOcc KPackageClause (ViewPackageClause (source_package f)) (Some root_id) RFilePackage pkg_id)
           else occ_decls' root_id 0 (Pos.succ pkg_id) (source_decls f) target
  end.

(* --- interval frame lemmas: an occurrence lookup outside a subtree's [me .. end] window is [None]. --- *)

Lemma end_expr_ge : forall e me, (me <= end_expr me e)%positive.
Proof.
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros me; try (cbn [end_expr]; lia);
    (cbn [end_expr]; specialize (IHx (Pos.succ me)); lia).
Qed.

Lemma occ_expr'_below : forall e parent role me target,
  (target < me)%positive -> occ_expr' parent role me e target = None.
Proof.
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent role me target Hlt; cbn [occ_expr'];
    try (destruct (Pos.eqb_spec target me); [lia|reflexivity]);
    (destruct (Pos.eqb_spec target me); [lia|]; apply IHx; lia).
Qed.

Lemma occ_expr'_above : forall e parent role me target,
  (end_expr me e < target)%positive -> occ_expr' parent role me e target = None.
Proof.
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent role me target Hgt; cbn [occ_expr' end_expr] in *;
    try (destruct (Pos.eqb_spec target me); [lia|reflexivity]);
    (pose proof (end_expr_ge x (Pos.succ me)) as Hx;
     destruct (Pos.eqb_spec target me); [lia|]; apply IHx; exact Hgt).
Qed.

Lemma next_exprs_ge : forall es me, (me <= next_exprs me es)%positive.
Proof.
  induction es as [|e rest IH]; intros me; cbn [next_exprs]; [lia|].
  specialize (IH (Pos.succ (end_expr me e))). pose proof (end_expr_ge e me) as He. lia.
Qed.

Lemma occ_exprs'_below : forall es parent aidx me target,
  (target < me)%positive -> occ_exprs' parent aidx me es target = None.
Proof.
  induction es as [|e rest IH]; intros parent aidx me target Hlt; cbn [occ_exprs']; [reflexivity|].
  pose proof (end_expr_ge e me) as He.
  destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
  - apply occ_expr'_below. exact Hlt.
  - lia.
Qed.

Lemma occ_exprs'_above : forall es parent aidx me target,
  (next_exprs me es <= target)%positive -> occ_exprs' parent aidx me es target = None.
Proof.
  induction es as [|e rest IH]; intros parent aidx me target Hge; cbn [occ_exprs' next_exprs] in *; [reflexivity|].
  pose proof (next_exprs_ge rest (Pos.succ (end_expr me e))) as Hn.
  destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
  - lia.
  - apply IH. lia.
Qed.

Lemma end_stmt_ge : forall s me, (me <= end_stmt me s)%positive.
Proof.
  intros [args] me. cbn [end_stmt]. pose proof (next_exprs_ge args (Pos.succ me)) as Hn. lia.
Qed.

Lemma occ_stmt'_below : forall s parent sidx me target,
  (target < me)%positive -> occ_stmt' parent sidx me s target = None.
Proof.
  intros [args] parent sidx me target Hlt. cbn [occ_stmt'].
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_exprs'_below. lia.
Qed.

Lemma occ_stmt'_above : forall s parent sidx me target,
  (end_stmt me s < target)%positive -> occ_stmt' parent sidx me s target = None.
Proof.
  intros [args] parent sidx me target Hgt. cbn [occ_stmt' end_stmt] in *.
  pose proof (next_exprs_ge args (Pos.succ me)) as Hn.
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_exprs'_above. lia.
Qed.

Lemma next_stmts_ge : forall ss me, (me <= next_stmts me ss)%positive.
Proof.
  induction ss as [|s rest IH]; intros me; cbn [next_stmts]; [lia|].
  specialize (IH (Pos.succ (end_stmt me s))). pose proof (end_stmt_ge s me) as Hs. lia.
Qed.

Lemma occ_stmts'_below : forall ss parent sidx me target,
  (target < me)%positive -> occ_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hlt; cbn [occ_stmts']; [reflexivity|].
  pose proof (end_stmt_ge s me) as Hs.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - apply occ_stmt'_below. exact Hlt.
  - lia.
Qed.

Lemma occ_stmts'_above : forall ss parent sidx me target,
  (next_stmts me ss <= target)%positive -> occ_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hge; cbn [occ_stmts' next_stmts] in *; [reflexivity|].
  pose proof (next_stmts_ge rest (Pos.succ (end_stmt me s))) as Hn.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - lia.
  - apply IH. lia.
Qed.

Lemma end_decl_ge : forall d me, (me <= end_decl me d)%positive.
Proof.
  intros [body] me. cbn [end_decl]. pose proof (next_stmts_ge body (Pos.succ me)) as Hn. lia.
Qed.

Lemma occ_decl'_below : forall d parent didx me target,
  (target < me)%positive -> occ_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hlt. cbn [occ_decl'].
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_stmts'_below. lia.
Qed.

Lemma occ_decl'_above : forall d parent didx me target,
  (end_decl me d < target)%positive -> occ_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hgt. cbn [occ_decl' end_decl] in *.
  pose proof (next_stmts_ge body (Pos.succ me)) as Hn.
  destruct (Pos.eqb_spec target me); [lia|]. apply occ_stmts'_above. lia.
Qed.

Lemma occ_decls'_below : forall ds parent didx me target,
  (target < me)%positive -> occ_decls' parent didx me ds target = None.
Proof.
  induction ds as [|d rest IH]; intros parent didx me target Hlt; cbn [occ_decls']; [reflexivity|].
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
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent role me t target; cbn [build_expr occ_expr'];
    (* leaves *)
    try (cbn [fst]; destruct (Pos.eqb_spec target me);
         [ subst; rewrite NodeTable.get_set_same; reflexivity
         | rewrite NodeTable.get_set_other by congruence; reflexivity ]);
    (* conversions: one operand child *)
    (pose proof (build_expr_end x me RConversionOperand (Pos.succ me) t) as He1;
     destruct (build_expr me RConversionOperand (Pos.succ me) x t) as [t1 e1] eqn:E1;
     cbn [snd] in He1; subst e1; cbn [fst];
     destruct (Pos.eqb_spec target me);
     [ subst; rewrite NodeTable.get_set_same; reflexivity
     | rewrite NodeTable.get_set_other by congruence;
       specialize (IHx me RConversionOperand (Pos.succ me) t target);
       rewrite E1 in IHx; cbn [fst] in IHx; exact IHx ]).
Qed.

Lemma build_arg_get : forall e parent aidx me t target,
  NodeTable.get target (fst (build_arg parent aidx me e t)) =
    match occ_expr' parent (RPrintlnArg aidx) me e target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof. intros. apply build_expr_get. Qed.

Lemma build_seq_arg_get : forall args parent aidx me t target,
  NodeTable.get target (fst (build_seq build_arg parent aidx me args t)) =
    match occ_exprs' parent aidx me args target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  induction args as [|e rest IH]; intros parent aidx me t target; cbn [build_seq occ_exprs'].
  - reflexivity.
  - pose proof (build_arg_end e parent aidx me t) as He.
    destruct (build_arg parent aidx me e t) as [t1 se] eqn:E1. cbn [snd] in He. subst se. cbn [fst].
    specialize (IH parent (S aidx) (Pos.succ (end_expr me e)) t1 target). rewrite IH.
    specialize (build_arg_get e parent aidx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
    + rewrite (occ_exprs'_below rest parent (S aidx) (Pos.succ (end_expr me e)) target ltac:(lia)). reflexivity.
    + rewrite (occ_expr'_above e parent (RPrintlnArg aidx) me target ltac:(lia)). reflexivity.
Qed.

Lemma build_stmt_get : forall s parent sidx me t target,
  NodeTable.get target (fst (build_stmt parent sidx me s t)) =
    match occ_stmt' parent sidx me s target with
    | Some o => Some (occurrence_meta o)
    | None   => NodeTable.get target t
    end.
Proof.
  intros [args] parent sidx me t target. cbn [build_stmt occ_stmt'].
  pose proof (build_seq_arg_next args me 0 (Pos.succ me) t) as Hnx.
  destruct (build_seq build_arg me 0 (Pos.succ me) args t) as [t1 nx] eqn:E1. cbn [snd] in Hnx. subst nx.
  cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite NodeTable.get_set_same. reflexivity.
  - rewrite NodeTable.get_set_other by congruence.
    specialize (build_seq_arg_get args me 0 (Pos.succ me) t target) as HG.
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

(* ============ the load-bearing UNIVERSAL exactness theorem (directive §9). ============ *)

(* the metadata the builder stores at EVERY local id is EXACTLY the metadata of the source occurrence that
   id designates — both presence (a real occurrence -> its meta) and absence (no occurrence -> no entry).
   It ranges over every positive id, needs no pre-existing reference, and never assumes the id is valid.
   A structurally-coherent MISLABELING (package clause as a declaration, leaf as a statement, shifted index,
   wrong parent/subtree, deduplicated repeated argument) makes the two sides disagree, so it CANNOT satisfy
   this equality. *)
Theorem build_file_source_exact : forall f local,
  NodeTable.get local (fi_table (build_file f)) = option_map occurrence_meta (source_occurrence_at f local).
Proof.
  intros f local. unfold build_file, source_occurrence_at.
  destruct (source_imports f) as [|i ?]; [| destruct i].
  set (tp := NodeTable.set pkg_id (mkMeta KPackageClause (Some root_id) RFilePackage pkg_id) NodeTable.empty).
  pose proof (build_seq_decl_next (source_decls f) root_id 0 (Pos.succ pkg_id) tp) as Hnx.
  destruct (build_seq build_decl root_id 0 (Pos.succ pkg_id) (source_decls f) tp) as [t1 nx] eqn:E1.
  cbn [snd] in Hnx. subst nx. cbn [fi_table].
  destruct (Pos.eqb_spec local root_id).
  - (* file root *)
    subst. rewrite NodeTable.get_set_same.
    cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
    unfold count_file. reflexivity.
  - rewrite NodeTable.get_set_other by congruence.
    specialize (build_seq_decl_get (source_decls f) root_id 0 (Pos.succ pkg_id) tp local) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.eqb_spec local pkg_id).
    + (* package clause: below the decl window, so the decl spec is None; read it out of [tp] *)
      subst local.
      rewrite (occ_decls'_below (source_decls f) root_id 0 (Pos.succ pkg_id) pkg_id
                 ltac:(unfold pkg_id; lia)).
      unfold tp. rewrite NodeTable.get_set_same.
      cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
      reflexivity.
    + (* declaration region: [tp] holds nothing here (local <> pkg_id), so both sides agree via the decl spec *)
      unfold tp. rewrite NodeTable.get_set_other by congruence. rewrite NodeTable.get_empty.
      destruct (occ_decls' root_id 0 (Pos.succ pkg_id) (source_decls f) local) as [o|];
        cbn [option_map]; reflexivity.
Qed.

(* --- the directive §9 consequences (A..H), all derived from the one universal theorem. --- *)

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

(* ================================================================================================= *)
(** ** PILLAR 2 — structural navigation invariants (directive §15-§18): preorder-interval ancestry,     *)
(*    exact parent lookup, interval-jump direct children, and canonical enumeration.  The [SubtreeWF] /  *)
(*    [ForestWF] machinery below is GRAMMAR-AGNOSTIC (it speaks only of the node table + preorder         *)
(*    intervals); it is reused unchanged from the accepted spike.  Only [build_*_spec] / [build_file_wf]  *)
(*    (which relate the real builders to that machinery) and [thm1_root_id_canonical] are grammar-aware.  *)
(* ================================================================================================= *)

(* preorder-interval ancestry: O(1) arithmetic on [subtree_end] after one map lookup. *)
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

Fixpoint pos_seq (start : positive) (len : nat) : list positive :=
  match len with O => [] | S n => start :: pos_seq (Pos.succ start) n end.

(* direct children by INTERVAL JUMP (directive §16): the cursor walks DIRECTLY from the first child to the
   parent's interval end, looking up ONLY the id at the cursor and, after each node, jumping the cursor PAST
   its whole subtree to [subtree_end+1] — it never constructs or traverses the skipped descendant ids.  So
   both the lookup count AND the number of recursive steps are O(#direct children), not O(#descendants). *)
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

(* --- structural invariants of the built index (grammar-agnostic; verbatim from the accepted spike). --- *)

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

Lemma forest_nil (t : NodeTable.table NodeMeta) P lo : ForestWF t t P lo lo.
Proof. constructor; intros; solve [ lia | reflexivity | exfalso; lia ]. Qed.

Lemma set_mono (tf : NodeTable.table NodeMeta) me meta :
  NodeTable.get me tf = None -> forall j m, NodeTable.get j tf = Some m -> NodeTable.get j (NodeTable.set me meta tf) = Some m.
Proof.
  intros Hfresh j m Hj. destruct (Pos.eq_dec j me) as [->|Hne].
  - rewrite Hfresh in Hj; discriminate.
  - rewrite NodeTable.get_set_other by congruence. exact Hj.
Qed.

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
  - subst p. apply Anc_dir. exact Hpid.
  - eapply Anc_step; [ | exact Hpid].
    apply IHk.
    + unfold ltof. apply Pos2Nat.inj_lt. exact Hpk.
    + lia.
    + lia.
Qed.

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
  assert (Hget_me : NodeTable.get me t = Some meta) by (unfold t; apply NodeTable.get_set_same).
  assert (Hget_ne : forall k, k <> me -> NodeTable.get k t = NodeTable.get k tf) by (intros; unfold t; apply NodeTable.get_set_other; congruence).
  split.
  - intros k Hk. rewrite Hget_ne by lia. apply Hff; exact Hk.
  - constructor.
    + exact Hmse.
    + intros k Hk. rewrite Hget_ne by lia. apply (for_out HF). lia.
    + exists meta. split; [exact Hget_me | split; [exact Hpar | exact Hend]].
    + intros k H1 H2. destruct (Pos.eq_dec k me) as [->|Hne].
      * rewrite Hget_me; discriminate.
      * rewrite Hget_ne by exact Hne. eapply (for_pres HF); [lia|lia].
    + intros k m H1 H2 Hm. destruct (Pos.eq_dec k me) as [->|Hne].
      * rewrite Hget_me in Hm; injection Hm as <-. rewrite Hend. lia.
      * rewrite Hget_ne in Hm by exact Hne.
        destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
    + intros k m H1 H2 Hm.
      rewrite Hget_ne in Hm by lia.
      destruct (for_prng HF k m ltac:(lia) ltac:(lia) Hm) as [p [Hpar' Hcase]].
      destruct Hcase as [Hpeq | [Hlo [Hpk [mp [Hmp [Hkmp Hmmp]]]]]].
      * subst p. exists me, meta. rewrite Hget_me.
        repeat split; try assumption; try (rewrite Hend); try lia.
        destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
      * exists p, mp. rewrite Hget_ne by lia.
        repeat split; try assumption; try lia.
    + intros a k ma H1 H2 Hget_a Hak Hkend.
      destruct (Pos.eq_dec a me) as [->|Hne].
      * rewrite Hget_me in Hget_a; injection Hget_a as <-. rewrite Hend in Hkend.
        eapply wrap_root_sound; [exact Hf0 | exact HF | exact Hfresh_me | lia | lia].
      * rewrite Hget_ne in Hget_a by exact Hne.
        assert (Hmono : forall j mm, NodeTable.get j tf = Some mm -> NodeTable.get j t = Some mm)
          by (intros; unfold t; apply set_mono; assumption).
        eapply ancestor_mono; [exact Hmono|].
        eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
Qed.

Lemma forest_cons (t0 t1 t2 : NodeTable.table NodeMeta) P me se nx :
  SubtreeWF t0 t1 (Some P) me se ->
  Fresh t1 (Pos.succ se) ->
  ForestWF t1 t2 P (Pos.succ se) nx ->
  ForestWF t0 t2 P me nx.
Proof.
  intros HS Hf1 HF.
  assert (Hmse : me <= se) by (apply (sub_le HS)).
  assert (Hsx : Pos.succ se <= nx) by (apply (for_le HF)).
  assert (Hmono : forall j m, NodeTable.get j t1 = Some m -> NodeTable.get j t2 = Some m).
  { intros j m Hj. destruct (Pos.ltb j (Pos.succ se)) eqn:Hlt.
    - apply Pos.ltb_lt in Hlt. rewrite (for_out HF j) by lia. exact Hj.
    - apply Pos.ltb_ge in Hlt. rewrite (Hf1 j) in Hj by lia. discriminate. }
  assert (Hout2 : forall k, k < Pos.succ se \/ nx <= k -> NodeTable.get k t2 = NodeTable.get k t1)
    by (intros; apply (for_out HF); lia).
  constructor.
  - lia.
  - intros k Hk. rewrite Hout2 by lia. apply (sub_out HS). lia.
  - intros k H1 H2. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge. eapply (for_pres HF); [lia|lia].
    + apply Pos.leb_gt in Hge. rewrite Hout2 by lia. eapply (sub_pres HS); [lia|lia].
  - intros k m H1 H2 Hm. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge. destruct (for_nest HF k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hm by lia.
      destruct (sub_nest HS k m ltac:(lia) ltac:(lia) Hm) as [A B]. lia.
  - intros k m H1 H2 Hm. destruct (Pos.leb (Pos.succ se) k) eqn:Hge.
    + apply Pos.leb_le in Hge.
      destruct (for_prng HF k m ltac:(lia) ltac:(lia) Hm) as [p [Hpar Hcase]].
      exists p. split; [exact Hpar|]. destruct Hcase as [->|[Hlo [Hpk [mp [Hmp Hb]]]]].
      * left; reflexivity.
      * right. split; [lia|split;[lia|]]. exists mp. split; [exact Hmp | exact Hb].
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hm by lia.
      destruct (Pos.eqb me k) eqn:Hmek.
      * apply Pos.eqb_eq in Hmek; subst k.
        destruct (sub_root HS) as [m0 [Hg [Hp He]]]. rewrite Hg in Hm; injection Hm as <-.
        exists P. split; [exact Hp | left; reflexivity].
      * apply Pos.eqb_neq in Hmek.
        destruct (sub_prng HS k m ltac:(lia) ltac:(lia) Hm) as [p [mp [Hpar [Hgp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
        exists p. split; [exact Hpar|]. right. split; [lia|split;[lia|]].
        exists mp. split; [ rewrite Hout2 by lia; exact Hgp | split; [exact Hb1 | exact Hb2] ].
  - intros a k ma H1 H2 Hget_a Hak Hkend.
    destruct (Pos.leb (Pos.succ se) a) eqn:Hge.
    + apply Pos.leb_le in Hge.
      assert (Hmono2 : forall j mm, NodeTable.get j t2 = Some mm -> NodeTable.get j t2 = Some mm) by auto.
      eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hget_a by lia.
      eapply ancestor_mono; [exact Hmono|].
      eapply (sub_snd HS); [lia|lia|exact Hget_a|exact Hak|].
      destruct (sub_nest HS a ma ltac:(lia) ltac:(lia) Hget_a) as [_ Hb]. lia.
Qed.

Lemma Fresh_weaken (t : NodeTable.table NodeMeta) from from' :
  from <= from' -> Fresh t from -> Fresh t from'.
Proof. intros H HF k Hk. apply HF. lia. Qed.

Lemma Fresh_empty (from : positive) : Fresh NodeTable.empty from.
Proof. intros k _; apply NodeTable.get_empty. Qed.

(* --- the real builders satisfy the WF machinery (grammar-aware). --- *)

Lemma build_expr_spec : forall e parent role me t0 t se,
  Fresh t0 me ->
  build_expr parent role me e t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  induction e as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent role me t0 t se Hf0 Hbuild; cbn [build_expr] in Hbuild;
    (* leaves: an empty children forest wrapped at [me] *)
    try (injection Hbuild as Ht Hse; subst t; subst se;
         eapply subtree_from_forest;
           [ reflexivity | exact Hf0 | apply forest_nil
           | (eapply Fresh_weaken; [|exact Hf0]; lia) | reflexivity | reflexivity ]);
    (* conversions: one operand child subtree wrapped at [me] *)
    (destruct (build_expr me RConversionOperand (Pos.succ me) x t0) as [t1 e1] eqn:E1;
     injection Hbuild as Ht Hse; subst t; subst se;
     assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia);
     destruct (IHx me RConversionOperand (Pos.succ me) t0 t1 e1 Hf0' E1) as [Hfr1 HS1];
     assert (HF : ForestWF t0 t1 me (Pos.succ me) (Pos.succ e1))
       by (eapply forest_cons; [exact HS1 | exact Hfr1 | apply forest_nil]);
     eapply subtree_from_forest;
       [ reflexivity | exact Hf0 | exact HF | exact Hfr1 | reflexivity | reflexivity ]).
Qed.

Lemma build_arg_spec : forall parent aidx me e t0 t se,
  Fresh t0 me ->
  build_arg parent aidx me e t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent aidx me e t0 t se Hf0 H. unfold build_arg in H.
  exact (build_expr_spec e parent (RPrintlnArg aidx) me t0 t se Hf0 H).
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

Lemma build_stmt_spec : forall parent sidx me s t0 t se,
  Fresh t0 me ->
  build_stmt parent sidx me s t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent sidx me [args] t0 t se Hf0 Hbuild; cbn [build_stmt] in Hbuild.
  destruct (build_seq build_arg me 0 (Pos.succ me) args t0) as [t1 nx1] eqn:E1.
  injection Hbuild as Ht Hse; subst t; subst se.
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia).
  destruct (build_seq_spec build_arg build_arg_spec args me 0 (Pos.succ me) t0 t1 nx1 Hf0' E1) as [Hfr1 HF1].
  assert (Hge : Pos.succ me <= nx1) by (apply (for_le HF1)).
  assert (Hnx : Pos.succ (Pos.pred nx1) = nx1)
    by (destruct (Pos.succ_pred_or nx1) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (NodeTable.set me (mkMeta KStatement (Some parent) (RDeclStmt sidx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (NodeTable.set me (mkMeta KStatement (Some parent) (RDeclStmt sidx) (Pos.pred nx1)) t1)
                        (Some parent) me (Pos.pred nx1)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | exact Hf0 | exact HF1 | exact Hfr1 | reflexivity | reflexivity ]. }
  rewrite Hnx. exact H.
Qed.

Lemma build_decl_spec : forall parent didx me d t0 t se,
  Fresh t0 me ->
  build_decl parent didx me d t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent didx me [body] t0 t se Hf0 Hbuild; cbn [build_decl] in Hbuild.
  destruct (build_seq build_stmt me 0 (Pos.succ me) body t0) as [t1 nx1] eqn:E1.
  injection Hbuild as Ht Hse; subst t; subst se.
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply Fresh_weaken; [|exact Hf0]; lia).
  destruct (build_seq_spec build_stmt build_stmt_spec body me 0 (Pos.succ me) t0 t1 nx1 Hf0' E1) as [Hfr1 HF1].
  assert (Hge : Pos.succ me <= nx1) by (apply (for_le HF1)).
  assert (Hnx : Pos.succ (Pos.pred nx1) = nx1)
    by (destruct (Pos.succ_pred_or nx1) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (NodeTable.set me (mkMeta KTopLevelDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (NodeTable.set me (mkMeta KTopLevelDecl (Some parent) (RFileDecl didx) (Pos.pred nx1)) t1)
                        (Some parent) me (Pos.pred nx1)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | exact Hf0 | exact HF1 | exact Hfr1 | reflexivity | reflexivity ]. }
  rewrite Hnx. exact H.
Qed.

Lemma build_file_wf (f : GoSourceFile) :
  SubtreeWF NodeTable.empty (fi_table (build_file f)) None root_id (fi_count (build_file f)).
Proof.
  unfold build_file. destruct (source_imports f) as [|i ?]; [| destruct i].
  set (pmeta := mkMeta KPackageClause (Some root_id) RFilePackage pkg_id).
  set (tp := NodeTable.set pkg_id pmeta NodeTable.empty).
  assert (HSpkg : Fresh tp (Pos.succ pkg_id) /\ SubtreeWF NodeTable.empty tp (Some root_id) pkg_id pkg_id).
  { unfold tp, pmeta. eapply subtree_from_forest;
      [ reflexivity | apply Fresh_empty | apply forest_nil | apply Fresh_empty | reflexivity | reflexivity ]. }
  destruct HSpkg as [Hfrpkg HSpkg].
  destruct (build_seq build_decl root_id 0 (Pos.succ pkg_id) (source_decls f) tp) as [t1 nx] eqn:E.
  cbn [fi_table fi_count].
  destruct (build_seq_spec build_decl build_decl_spec (source_decls f) root_id 0 (Pos.succ pkg_id)
              tp t1 nx Hfrpkg E) as [Hfr HFdecls].
  assert (HF : ForestWF NodeTable.empty t1 root_id pkg_id nx)
    by (eapply forest_cons; [exact HSpkg | exact Hfrpkg | exact HFdecls]).
  assert (Hge : Pos.succ pkg_id <= nx) by (apply (for_le HFdecls)).
  assert (Hnx : Pos.succ (Pos.pred nx) = nx)
    by (destruct (Pos.succ_pred_or nx) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (NodeTable.set root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1) nx /\
              SubtreeWF NodeTable.empty (NodeTable.set root_id (mkMeta KFile None RFileRoot (Pos.pred nx)) t1)
                        None root_id (Pos.pred nx)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | apply Fresh_empty | exact HF | exact Hfr | reflexivity | reflexivity ]. }
  destruct H as [_ HS]. exact HS.
Qed.

(* --- enumeration helpers over the preorder id interval (grammar-agnostic; verbatim). --- *)

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

(* --- the navigation theorem set (directive §15-§18); grammar-agnostic given [build_file_wf]. --- *)

Lemma in_domain (f : GoSourceFile) k m :
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

(* §23.1 — the root id is canonical: every file root occupies the SAME fixed local id [root_id]. *)
Theorem thm1_root_id_canonical (f : GoSourceFile) :
  exists m, NodeTable.get root_id (fi_table (build_file f)) = Some m /\ nm_kind m = KFile /\ nm_role m = RFileRoot.
Proof.
  unfold build_file. destruct (source_imports f) as [|i ?]; [| destruct i].
  destruct (build_seq build_decl root_id 0 (Pos.succ pkg_id) (source_decls f)
              (NodeTable.set pkg_id (mkMeta KPackageClause (Some root_id) RFilePackage pkg_id) NodeTable.empty))
    as [t1 nx] eqn:E.
  exists (mkMeta KFile None RFileRoot (Pos.pred nx)).
  cbn [fi_table]. rewrite NodeTable.get_set_same. split; [reflexivity | split; reflexivity].
Qed.

(* §23.29/§23.30 — the root has no parent, and ONLY the root has no parent. *)
Theorem thm2_root_no_parent (f : GoSourceFile) m :
  NodeTable.get root_id (fi_table (build_file f)) = Some m -> nm_parent m = None.
Proof.
  intros H. pose proof (build_file_wf f) as WF. destruct (sub_root WF) as [m0 [Hg [Hp _]]].
  rewrite Hg in H. injection H as <-. exact Hp.
Qed.

Theorem thm3_nonroot_has_parent (f : GoSourceFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m -> k <> root_id -> exists p, nm_parent m = Some p.
Proof.
  intros H Hne. pose proof (build_file_wf f) as WF.
  destruct (in_domain f k m H) as [Hlo Hhi].
  assert (root_id < k) by lia.
  destruct (sub_prng WF k m ltac:(lia) Hhi H) as [p [mp [Hpar _]]]. exists p; exact Hpar.
Qed.

Theorem thm3b_parent_unique (f : GoSourceFile) k m p1 p2 :
  NodeTable.get k (fi_table (build_file f)) = Some m -> nm_parent m = Some p1 -> nm_parent m = Some p2 -> p1 = p2.
Proof. intros _ H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* §23.42 (completeness half) — ancestry implies nested preorder intervals. *)
Lemma anc_complete (f : GoSourceFile) a d :
  Ancestor (fi_table (build_file f)) a d ->
  exists ma md, NodeTable.get a (fi_table (build_file f)) = Some ma /\
                NodeTable.get d (fi_table (build_file f)) = Some md /\
                a < d /\ d <= nm_subtree_end ma /\ nm_subtree_end md <= nm_subtree_end ma.
Proof.
  pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  induction 1 as [a d Hp | a p c Hac IH Hp].
  - unfold parent_id in Hp. destruct (NodeTable.get d t) as [md|] eqn:Ed; [|discriminate].
    destruct (in_domain f d md Ed) as [Hlo Hhi].
    assert (Hdne : d <> root_id).
    { intro; subst d. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ed; injection Ed as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF d md ltac:(lia) Hhi Ed) as [p [mp [Hpar [Hmp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-.
    exists mp, md. repeat split; try assumption; lia.
  - unfold parent_id in Hp. destruct (NodeTable.get c t) as [mc|] eqn:Ec; [|discriminate].
    destruct IH as [ma [mp0 [Hga [Hgp [Hap [Hpend Hmpend]]]]]].
    destruct (in_domain f c mc Ec) as [Hlo Hhi].
    assert (Hcne : c <> root_id).
    { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ec; injection Ec as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF c mc ltac:(lia) Hhi Ec) as [p' [mp' [Hpar [Hmp' [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-. rewrite Hgp in Hmp'. injection Hmp' as <-.
    exists ma, mc. repeat split; try assumption; lia.
Qed.

Definition parentb (t : NodeTable.table NodeMeta) (c pid : positive) : bool :=
  match NodeTable.get c t with
  | Some mc => match nm_parent mc with Some p => Pos.eqb p pid | None => false end
  | None => false
  end.

Lemma anc_parent_ge (f : GoSourceFile) a d p :
  Ancestor (fi_table (build_file f)) a d ->
  parent_id (fi_table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Hanc Hp. inversion Hanc; subst.
  - rewrite H in Hp. injection Hp as <-. lia.
  - rewrite H0 in Hp. injection Hp as <-.
    destruct (anc_complete f a _ H) as [ma [md [_ [_ [Hlt _]]]]]. lia.
Qed.

Lemma desc_parent_ge (f : GoSourceFile) a ma d p :
  NodeTable.get a (fi_table (build_file f)) = Some ma ->
  (a < d)%positive -> (d <= nm_subtree_end ma)%positive ->
  parent_id (fi_table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Ha Hlt Hle Hp. pose proof (build_file_wf f) as WF.
  destruct (in_domain f a ma Ha) as [Hlo Hhi].
  eapply anc_parent_ge; [ eapply (sub_snd WF a d ma); [lia|lia|exact Ha|exact Hlt|exact Hle] | exact Hp ].
Qed.

Lemma child_gt (f : GoSourceFile) pid c mc :
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

Lemma first_child (f : GoSourceFile) pid mp :
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

Lemma next_child (f : GoSourceFile) pid mp c mc :
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
  assert (Hpge : (pid <= p)%positive)
    by (eapply (desc_parent_ge f pid mp d p Hpid); [lia|lia|unfold parent_id; rewrite Ed; exact Hparp]).
  destruct (in_domain f p mpp Hgetp) as [Hlop Hhip].
  assert (Hp_eq : p = pid).
  { destruct (Pos.eq_dec p pid) as [->|Hne]; [reflexivity|]. exfalso.
    assert (Hpgt : (pid < p)%positive) by lia.
    destruct (Pos.leb c p) eqn:Hcp.
    - apply Pos.leb_le in Hcp.
      assert (Hpsub : (nm_subtree_end mpp <= nm_subtree_end mc)%positive).
      { destruct (Pos.eq_dec p c) as [->|Hpc2].
        - rewrite Hgetp in Hc. injection Hc as <-. lia.
        - destruct (anc_complete f c p (sub_snd WF c p mc ltac:(lia) Hhi_c Hc ltac:(lia) ltac:(lia)))
            as [mc' [mpp' [Hgc [Hgp [_ [_ Hend]]]]]].
          rewrite Hc in Hgc; injection Hgc as <-. rewrite Hgetp in Hgp; injection Hgp as <-. lia. }
      unfold d in Hb1. lia.
    - apply Pos.leb_gt in Hcp.
      assert (Hcanc : Ancestor (fi_table (build_file f)) p c).
      { eapply (sub_snd WF p c mpp); [lia|exact Hhip|exact Hgetp|lia|]. unfold d in Hb1. lia. }
      assert (p <= pid)%positive by (eapply anc_parent_ge; [exact Hcanc | unfold parent_id; rewrite Hc; exact Hpar]).
      lia. }
  unfold parent_id. rewrite Ed. rewrite Hparp. rewrite Hp_eq. reflexivity.
Qed.

Lemma interior_not_child (f : GoSourceFile) pid cur mcur k :
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

Lemma built_nested (f : GoSourceFile) x mx :
  NodeTable.get x (fi_table (build_file f)) = Some mx -> (x <= nm_subtree_end mx)%positive.
Proof.
  intros Hx. pose proof (build_file_wf f) as WF. destruct (in_domain f x mx Hx) as [Hlo Hhi].
  destruct (sub_nest WF x mx Hlo Hhi Hx) as [A _]. exact A.
Qed.

Lemma child_enum_sound : forall t pid limit cursor c,
  In c (child_enum t pid limit cursor) -> parent_id t c = Some pid.
Proof.
  intros t pid limit cursor c.
  functional induction (child_enum t pid limit cursor); intros Hin;
    try (exfalso; exact Hin); try (exact (IHl Hin)).
  apply in_inv in Hin. destruct Hin as [Heq|Hin]; [|exact (IHl Hin)].
  subst c. unfold parent_id. rewrite e0. cbn. rewrite e1. apply Pos.eqb_eq in e2. rewrite e2. reflexivity.
Qed.

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

Lemma child_enum_SS : forall t pid limit cursor,
  StronglySorted Pos.lt (child_enum t pid limit cursor).
Proof.
  intros t pid limit cursor.
  functional induction (child_enum t pid limit cursor); try (solve [constructor]); try exact IHl.
  constructor; [exact IHl|].
  apply Forall_forall. intros y Hy. apply child_enum_ge in Hy.
  pose proof (Pos.le_max_l (Pos.succ cursor) (Pos.succ (nm_subtree_end mc))). lia.
Qed.

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
  assert (HEcur : (nm_subtree_end mcur < c)%positive).
  { destruct (Pos.leb c (nm_subtree_end mcur)) eqn:Hb; [|apply Pos.leb_gt in Hb; lia].
    apply Pos.leb_le in Hb. exfalso.
    pose proof (interior_not_child f pid cur mcur c Hcur Hpar Hcurlt Hb) as Hnc.
    assert (parentb (fi_table (build_file f)) c pid = true)
      by (unfold parentb; rewrite Hc; cbn; rewrite Hpc; cbn; apply Pos.eqb_refl).
    congruence. }
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

(* §23.41/§23.43 — the O(1) preorder-interval ancestor test is sound AND complete. *)
Theorem thm13_interval_ancestry (f : GoSourceFile) a d :
  NodeTable.get a (fi_table (build_file f)) <> None ->
  (is_ancestor_local (fi_table (build_file f)) a d = true <-> Ancestor (fi_table (build_file f)) a d).
Proof.
  intros Ha. pose proof (build_file_wf f) as WF.
  set (t := fi_table (build_file f)) in *.
  unfold is_ancestor_local. destruct (NodeTable.get a t) as [ma|] eqn:Ea; [|congruence].
  split.
  - intros Hb. apply andb_true_iff in Hb as [H1 H2].
    apply Pos.ltb_lt in H1. apply Pos.leb_le in H2.
    destruct (in_domain f a ma Ea) as [Hlo Hhi].
    eapply (sub_snd WF); [lia|exact Hhi|exact Ea|exact H1|exact H2].
  - intros Hanc. destruct (anc_complete f a d Hanc) as [ma' [md [Hga [_ [Had [Hdend _]]]]]].
    unfold t in Ea. assert (ma = ma') by congruence. subst ma'.
    apply andb_true_iff; split; [apply Pos.ltb_lt; lia | apply Pos.leb_le; lia].
Qed.

(* §23.36 (children source order). *)
Theorem thm11_children_sorted (f : GoSourceFile) p :
  StronglySorted Pos.lt (child_ids (fi_table (build_file f)) p).
Proof.
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [m|] eqn:Ep; [|constructor].
  apply child_enum_SS.
Qed.

(* §23.34/§23.35/§23.38 — parent/child are inverse (interval-jump enumeration is sound + complete). *)
Theorem thm4_child_has_parent (f : GoSourceFile) p c :
  In c (child_ids (fi_table (build_file f)) p) -> parent_id (fi_table (build_file f)) c = Some p.
Proof.
  unfold child_ids. destruct (NodeTable.get p (fi_table (build_file f))) as [mp|] eqn:Ep; [|intros []].
  apply child_enum_sound.
Qed.

Theorem thm4_parent_has_child (f : GoSourceFile) p c mc :
  NodeTable.get c (fi_table (build_file f)) = Some mc -> nm_parent mc = Some p ->
  In c (child_ids (fi_table (build_file f)) p).
Proof.
  intros Hc Hpar. pose proof (build_file_wf f) as WF.
  pose proof (child_gt f p c mc Hc Hpar) as Hpc.
  destruct (in_domain f c mc Hc) as [Hlo Hhi].
  assert (Hcne : c <> root_id)
    by (intro; subst c; destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]; rewrite Hg in Hc; injection Hc as <-;
        rewrite Hp0 in Hpar; discriminate).
  destruct (sub_prng WF c mc ltac:(lia) Hhi Hc) as [p' [mp' [Hpar' [Hgp [_ [_ [Hcbound _]]]]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  assert (HpE : (p < nm_subtree_end mp')%positive) by lia.
  pose proof (first_child f p mp' Hgp HpE) as Hfc. unfold parent_id in Hfc.
  destruct (NodeTable.get (Pos.succ p) (fi_table (build_file f))) as [m1|] eqn:E1; [|discriminate].
  unfold child_ids. rewrite Hgp.
  eapply (child_enum_reaches _ f p mp' (Pos.succ p) m1 c mc);
    [ exact Hgp | exact E1 | exact Hfc | exact Hc | exact Hpar | lia | exact Hcbound | reflexivity ].
Qed.

(* §18/§23.40 — every occurrence appears EXACTLY ONCE in canonical preorder enumeration. *)
Definition all_ids (fi : FileIndex) : list positive := pos_seq root_id (Pos.to_nat (fi_count fi)).

Theorem thm7_enum_nodup (f : GoSourceFile) : NoDup (all_ids (build_file f)).
Proof. apply pos_seq_NoDup. Qed.

Theorem thm7_enum_complete (f : GoSourceFile) k m :
  NodeTable.get k (fi_table (build_file f)) = Some m -> In k (all_ids (build_file f)).
Proof.
  intros H. destruct (in_domain f k m H) as [Hlo Hhi]. unfold all_ids.
  apply pos_seq_In. unfold root_id. rewrite Pos2Nat.inj_1.
  assert (Pos.to_nat k <= Pos.to_nat (fi_count (build_file f)))%nat by (apply Pos2Nat.inj_le; exact Hhi).
  assert (1 <= Pos.to_nat k)%nat by (pose proof (Pos2Nat.is_pos k); lia).
  lia.
Qed.

Theorem thm7_enum_sound (f : GoSourceFile) k :
  In k (all_ids (build_file f)) -> NodeTable.get k (fi_table (build_file f)) <> None.
Proof.
  unfold all_ids. intros Hin. apply pos_seq_In in Hin. unfold root_id in Hin. rewrite Pos2Nat.inj_1 in Hin.
  pose proof (build_file_wf f) as WF. apply (sub_pres WF).
  - unfold root_id. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_1. lia.
  - apply Pos2Nat.inj_le. lia.
Qed.

(* §23.11/§23.12 — the builder branches only on tree SHAPE, and metadata is not a subtree copy. *)
Fixpoint same_shape (e1 e2 : GoExpr) : Prop :=
  match e1, e2 with
  | EIntConvert _ x1, EIntConvert _ x2 => same_shape x1 x2
  | EFloatConvert _ x1, EFloatConvert _ x2 => same_shape x1 x2
  | EComplexConvert _ x1, EComplexConvert _ x2 => same_shape x1 x2
  | EBool _, EBool _ => True
  | EInt _, EInt _ => True
  | ENeg _, ENeg _ => True
  | EString _, EString _ => True
  | EFloat _, EFloat _ => True
  | EComplex _, EComplex _ => True
  | _, _ => False
  end.

(* two expressions of the same SHAPE (ignoring every leaf payload and every conversion type tag) build to
   the IDENTICAL table — so the builder cannot be comparing / deduplicating subtrees by their content. *)
Theorem thm_builder_no_structural_search :
  forall e1 e2 parent role me t,
    same_shape e1 e2 -> build_expr parent role me e1 t = build_expr parent role me e2 t.
Proof.
  induction e1 as [ b | n1 | n2 | s | it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros [ b2 | n1' | n2' | s2 | it2 x2 | df2 | ft2 x2 | dcx2 | ct2 x2 ] parent role me t Hsh;
    cbn [same_shape] in Hsh; try contradiction; try reflexivity;
    (cbn [build_expr]; rewrite (IHx x2 me RConversionOperand (Pos.succ me) t Hsh);
     destruct (build_expr me RConversionOperand (Pos.succ me) x2 t) as [t1 e1]; reflexivity).
Qed.

Theorem thm14_meta_stores_no_subtree :
  forall m : NodeMeta, exists k op r e,
    m = mkMeta k op r e /\ (forall e', mkMeta k op r e = mkMeta k op r e' -> e = e').
Proof. intros [k op r e]. exists k, op, r, e. split; [reflexivity|]. intros e' H; injection H as <-; reflexivity. Qed.
