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

From Stdlib Require Import PArith NArith List Bool Lia Sorted Recdef Wf_nat Arith Eqdep_dec String.
From Fido Require Import FilePath Collections Ints Floats Complexes ModulePath GoVersion GoAST.
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

(* ================================================================================================= *)
(** ** PILLAR 3 — snapshot-indexed references over the exact [GoProgram] (directive §10-§17).           *)
(*    A reference belongs to the EXACT immutable program snapshot [p] (it is indexed by [p]), never to  *)
(*    free-standing index data — so two programs sharing a file map but differing in [ModuleSpec], or    *)
(*    sharing a shape but differing in payload, have NON-INTERCHANGEABLE reference types.  Structurally  *)
(*    guaranteed queries are TOTAL; only [parent_of] is optional (a file root has no parent).            *)
(* ================================================================================================= *)

(* decidable equality for the raw syntax (for UIP over the reference proof fields). *)
Definition decimalfloat_eq_dec (a b : DecimalFloat) : {a = b} + {a <> b}.
Proof.
  destruct (Floats.dm_eqb a b) eqn:E; [ left; apply Floats.dm_eqb_eq; exact E | right ].
  intro H; subst; rewrite (proj2 (Floats.dm_eqb_eq b b) eq_refl) in E; discriminate.
Defined.
Definition decimalcomplex_eq_dec (a b : DecimalComplex) : {a = b} + {a <> b}.
Proof. decide equality; apply decimalfloat_eq_dec. Defined.
Definition integertype_eq_dec (a b : IntegerType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition floattype_eq_dec (a b : FloatType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition complextype_eq_dec (a b : ComplexType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition goexpr_eq_dec (a b : GoExpr) : {a = b} + {a <> b}.
Proof.
  decide equality;
    first [ apply Bool.bool_dec | apply N.eq_dec | apply string_dec
          | apply integertype_eq_dec | apply floattype_eq_dec | apply complextype_eq_dec
          | apply decimalfloat_eq_dec | apply decimalcomplex_eq_dec ].
Defined.
Definition gostmt_eq_dec (a b : GoStmt) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec goexpr_eq_dec). Defined.
Definition godecl_eq_dec (a b : GoDecl) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec gostmt_eq_dec). Defined.
Definition packageclause_eq_dec (a b : PackageClauseSyntax) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition importspec_eq_dec (a b : ImportSpecSyntax) : {a = b} + {a <> b}.
Proof. destruct a. Defined.
Definition gosourcefile_eq_dec (a b : GoSourceFile) : {a = b} + {a <> b}.
Proof.
  decide equality;
    first [ apply (list_eq_dec godecl_eq_dec) | apply (list_eq_dec importspec_eq_dec)
          | apply packageclause_eq_dec ].
Defined.
Definition option_gosourcefile_eq_dec (a b : option GoSourceFile) : {a = b} + {a <> b}.
Proof. decide equality; apply gosourcefile_eq_dec. Defined.

Lemma fp_eq_dec (a b : FilePath) : {a = b} + {a <> b}.
Proof.
  destruct (fp_eqb a b) eqn:E; [left; apply fp_eqb_eq; exact E|].
  right; intro Heq; subst; rewrite (proj2 (fp_eqb_eq b b) eq_refl) in E; discriminate.
Qed.

(* the outer program index: a STANDARD FilePath map [FileMap.t FileIndex] keyed DIRECTLY by path — the
   standard [map] of [build_file] over the program's source files, so ONE map lookup reaches a file's index. *)
Module OFM := Collections.FileMapBase.
Module OFMF := Collections.FileMapFacts.
Definition outer_of (fm : GoFileMap) : OFM.t FileIndex := OFM.map build_file fm.
Lemma outer_get_exact : forall fm path,
  OFM.find path (outer_of fm)
  = match OFM.find path fm with Some f => Some (build_file f) | None => None end.
Proof. intros fm path. unfold outer_of. rewrite OFMF.map_o. destruct (OFM.find path fm); reflexivity. Qed.
Lemma outer_get_at : forall fm path f,
  OFM.find path fm = Some f -> OFM.find path (outer_of fm) = Some (build_file f).
Proof. intros fm path f H. rewrite outer_get_exact, H. reflexivity. Qed.

(* a local id is a real occurrence of file [f] iff it resolves in [f]'s built per-file table. *)
Definition valid_localb (f : GoSourceFile) (local : positive) : bool :=
  match NodeTable.get local (fi_table (build_file f)) with Some _ => true | None => false end.

(* the public raw occurrence key: file PATH (the map-key identity) + file-local preorder id. *)
Record NodeKey := mkKey { nk_file : FilePath ; nk_local : positive }.
Definition nodekey_eqb (a b : NodeKey) : bool :=
  fp_eqb (nk_file a) (nk_file b) && Pos.eqb (nk_local a) (nk_local b).

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

(* a child id of any node is a real occurrence — used to build validated child references without drops. *)
Lemma child_ids_parent (t : NodeTable.table NodeMeta) (pid c : positive) :
  In c (child_ids t pid) -> parent_id t c = Some pid.
Proof. unfold child_ids. destruct (NodeTable.get pid t) as [m|]; [|intros []]. apply child_enum_sound. Qed.

(* the canonical preorder id enumeration [pos_seq] is strictly increasing (source order). *)
Lemma pos_seq_sorted (start : positive) (len : nat) : StronglySorted Pos.lt (pos_seq start len).
Proof.
  revert start; induction len as [|n IH]; intros start; cbn [pos_seq]; [constructor|].
  constructor; [apply IH|]. apply Forall_forall. intros y Hy. apply pos_seq_In in Hy.
  rewrite Pos2Nat.inj_succ in Hy. apply Pos2Nat.inj_lt. lia.
Qed.

(* every file has a root occurrence at [root_id], so the root is always a valid local id. *)
Lemma root_valid (f : GoSourceFile) : valid_localb f root_id = true.
Proof. unfold valid_localb. destruct (thm1_root_id_canonical f) as [m [Hg _]]. rewrite Hg. reflexivity. Qed.

(* every id in the canonical enumeration of a file is a valid occurrence of it (no drops). *)
Lemma all_ids_valid (f : GoSourceFile) :
  forall c, In c (all_ids (build_file f)) -> valid_localb f c = true.
Proof.
  intros c Hin. unfold valid_localb.
  destruct (NodeTable.get c (fi_table (build_file f))) eqn:E; [reflexivity|].
  exfalso. exact (thm7_enum_sound f c Hin E).
Qed.

(* The public interface of the reference layer.  It exposes the abstract PROGRAM-indexed types, the validated
   MINTING boundaries, the projections, the TOTAL navigation API, and the theorem surfaces — but NOT the raw
   record constructors nor the raw index map.  Sealing the module against this signature makes "the only way
   to mint a reference is a validated function" TRUE rather than aspirational.  Every reference is indexed by
   the EXACT [GoProgram] snapshot. *)
Module Type SNAP_SIG.
  Parameter FileRef     : GoProgram -> Type.
  Parameter NodeRef     : GoProgram -> Type.
  Parameter SyntaxIndex : GoProgram -> Type.
  Parameter index_program : forall p, SyntaxIndex p.
  Parameter file_of_path : forall p, FilePath -> option (FileRef p).
  Parameter ref_of_key   : forall p, SyntaxIndex p -> NodeKey -> option (NodeRef p).
  Parameter file_ref_source : forall {p}, FileRef p -> GoSourceFile.
  Parameter file_ref_path : forall {p}, FileRef p -> FilePath.
  Parameter node_ref_file  : forall {p}, NodeRef p -> FileRef p.
  Parameter node_ref_local : forall {p}, NodeRef p -> positive.
  Parameter node_ref_valid : forall {p} (r : NodeRef p),
    valid_localb (file_ref_source (node_ref_file r)) (node_ref_local r) = true.
  Parameter node_ref_key   : forall {p}, NodeRef p -> NodeKey.
  Parameter ref_meta         : forall {p}, SyntaxIndex p -> NodeRef p -> NodeMeta.
  Parameter node_kind        : forall {p}, SyntaxIndex p -> NodeRef p -> SyntaxKind.
  Parameter node_role        : forall {p}, SyntaxIndex p -> NodeRef p -> NodeRole.
  Parameter node_subtree_end : forall {p}, SyntaxIndex p -> NodeRef p -> positive.
  Parameter containing_file  : forall {p}, NodeRef p -> FileRef p.
  Parameter parent_of        : forall {p}, SyntaxIndex p -> NodeRef p -> option (NodeRef p).
  Parameter children_of      : forall {p}, SyntaxIndex p -> NodeRef p -> list (NodeRef p).
  Parameter node_at          : forall {p}, NodeRef p -> option GoExpr.
  Parameter source_occurrence_of_ref : forall {p}, NodeRef p -> SourceOccurrence.
  Parameter is_ancestor_ref  : forall {p}, SyntaxIndex p -> NodeRef p -> NodeRef p -> bool.
  (* identity + total-API correctness *)
  Parameter node_ref_ext : forall p (r1 r2 : NodeRef p),
    node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
  Parameter thm_node_kind : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_kind idx r = nm_kind (ref_meta idx r).
  Parameter thm_node_role : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_role idx r = nm_role (ref_meta idx r).
  Parameter thm_ref_meta_built : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
  Parameter thm_containing_file : forall p (r : NodeRef p),
    containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = nk_file (node_ref_key r).
  Parameter node_ref_key_inj : forall p (r1 r2 : NodeRef p),
    node_ref_key r1 = node_ref_key r2 -> r1 = r2.
  Parameter file_ref_path_inj : forall p (fr1 fr2 : FileRef p),
    file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
  (* navigation *)
  Parameter thm_parent_root : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_ref_local r = root_id -> parent_of idx r = None.
  Parameter thm_parent_nonroot : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
  Parameter thm_parent_same_file : forall p (idx : SyntaxIndex p) (r pr : NodeRef p),
    parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
  Parameter thm_children_same_file : forall p (idx : SyntaxIndex p) (r cr : NodeRef p),
    In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
  Parameter thm_child_parent : forall p (idx : SyntaxIndex p) (r cr : NodeRef p),
    In cr (children_of idx r) -> parent_of idx cr = Some r.
  Parameter thm_parent_child : forall p (idx : SyntaxIndex p) (r pr : NodeRef p),
    parent_of idx r = Some pr -> In r (children_of idx pr).
  Parameter thm_children_of_source_order : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
  Parameter thm_children_of_nodup : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    NoDup (children_of idx r).
  (* minting boundaries: sound + complete, non-circular source membership *)
  Parameter ref_of_key_sound : forall p (idx : SyntaxIndex p) (k : NodeKey) (r : NodeRef p),
    ref_of_key p idx k = Some r -> node_ref_key r = k.
  Parameter ref_of_key_complete : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    ref_of_key p idx (node_ref_key r) = Some r.
  Parameter file_of_path_complete : forall p (fr : FileRef p),
    file_of_path p (file_ref_path fr) = Some fr.
  Parameter file_of_path_source : forall p (path : FilePath) (f : GoSourceFile),
    find_file path (prog_files p) = Some f ->
    exists fr, file_of_path p path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
  Parameter ref_of_key_source : forall p (idx : SyntaxIndex p) (path : FilePath) (f : GoSourceFile) (local : positive),
    find_file path (prog_files p) = Some f -> valid_localb f local = true ->
    exists r, ref_of_key p idx (mkKey path local) = Some r
              /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
  (* ref-level ancestry: the O(1) interval test, sound + complete vs the parent_of closure. *)
  Inductive RefAncestor (p : GoProgram) (idx : SyntaxIndex p) : NodeRef p -> NodeRef p -> Prop :=
  | RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor p idx a d
  | RAnc_step : forall a q d, RefAncestor p idx a q -> parent_of idx d = Some q -> RefAncestor p idx a d.
  Parameter thm_ref_ancestry : forall p (idx : SyntaxIndex p) (a d : NodeRef p),
    is_ancestor_ref idx a d = true <-> RefAncestor p idx a d.
  (* EXACT source-occurrence correspondence lifted through the sealed API: a valid reference's metadata IS
     its exact source occurrence's metadata (kind/role/parent/subtree), the reference's occurrence IS the
     independent spec's occurrence (pinning the VIEW), node_at agrees with the source view, and parent_of
     returns the EXACT source parent. *)
  Parameter ref_meta_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
  Parameter node_kind_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
  Parameter node_role_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_role idx r = occurrence_role (source_occurrence_of_ref r).
  Parameter node_parent_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    nm_parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
  Parameter node_subtree_end_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
  Parameter source_occ_of_ref_eq : forall {p} (r : NodeRef p),
    source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) = Some (source_occurrence_of_ref r).
  Parameter node_at_matches_source_view : forall {p} (r : NodeRef p),
    node_at r = view_expr (source_occurrence_of_ref r).
  Parameter node_parent_ref_matches_source : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    match occurrence_parent (source_occurrence_of_ref r) with
    | None     => parent_of idx r = None
    | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
    end.
  (* minting soundness for FileRef + the rejection cases (invalid path / invalid local id). *)
  Parameter file_of_path_sound : forall p (fp : FilePath) (fr : FileRef p),
    file_of_path p fp = Some fr -> file_ref_path fr = fp.
  Parameter file_of_path_source_exact : forall p (fp : FilePath) (fr : FileRef p),
    file_of_path p fp = Some fr -> find_file fp (prog_files p) = Some (file_ref_source fr).
  Parameter ref_of_key_invalid_path : forall p (idx : SyntaxIndex p) (fp : FilePath) (local : positive),
    find_file fp (prog_files p) = None -> ref_of_key p idx (mkKey fp local) = None.
  Parameter ref_of_key_invalid_local : forall p (idx : SyntaxIndex p) (fp : FilePath) (f : GoSourceFile) (local : positive),
    find_file fp (prog_files p) = Some f -> valid_localb f local = false -> ref_of_key p idx (mkKey fp local) = None.
  (* decidable NodeRef equality (reference identity IS NodeKey identity). *)
  Parameter noderef_eq_dec : forall {p} (r1 r2 : NodeRef p), {r1 = r2} + {r1 <> r2}.
  (* the file-root reference + the CANONICAL preorder enumeration of ALL a file's references, and reachability
     of every occurrence from the file root by repeated parent links. *)
  Parameter file_root_ref : forall {p}, FileRef p -> NodeRef p.
  Parameter file_root_ref_local : forall p (fr : FileRef p), node_ref_local (file_root_ref fr) = root_id.
  Parameter file_root_ref_file : forall p (fr : FileRef p), node_ref_file (file_root_ref fr) = fr.
  (* the canonical reference enumeration REUSES the passed SyntaxIndex (one outer-map lookup for the file's
     precomputed FileIndex) — it does NOT rebuild the per-file index. *)
  Parameter file_refs : forall {p}, SyntaxIndex p -> FileRef p -> list (NodeRef p).
  Parameter file_refs_same_file : forall p (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p),
    In r (file_refs idx fr) -> node_ref_file r = fr.
  Parameter file_refs_complete : forall p (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p),
    node_ref_file r = fr -> In r (file_refs idx fr).
  Parameter file_refs_nodup : forall p (idx : SyntaxIndex p) (fr : FileRef p), NoDup (file_refs idx fr).
  Parameter file_refs_source_order : forall p (idx : SyntaxIndex p) (fr : FileRef p),
    StronglySorted Pos.lt (map node_ref_local (file_refs idx fr)).
  Parameter file_root_ref_in_refs : forall p (idx : SyntaxIndex p) (fr : FileRef p),
    In (file_root_ref fr) (file_refs idx fr).
  (* reachability: every occurrence reaches the file root by repeated parent links (the root is a strict
     ancestor of every non-root occurrence), and every enumerated reference is the root or reachable from it. *)
  Parameter thm_reachable_from_root : forall p (idx : SyntaxIndex p) (r : NodeRef p),
    node_ref_local r <> root_id -> RefAncestor p idx (file_root_ref (node_ref_file r)) r.
  Parameter thm_refs_reachable : forall p (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p),
    In r (file_refs idx fr) -> r = file_root_ref fr \/ RefAncestor p idx (file_root_ref fr) r.
End SNAP_SIG.

Module Snap : SNAP_SIG.

(* a file-root handle for ONE file occurrence of program [p]: the file's PATH (its public identity) + its
   source + a STANDARD-MAP membership proof.  No hidden slot: the path IS the map key. *)
Record FileRef_T (p : GoProgram) := mkFileRef {
  file_ref_path   : FilePath;
  file_ref_source : GoSourceFile;
  file_ref_at     : OFM.find file_ref_path (prog_files p) = Some file_ref_source
}.
Arguments file_ref_path   {p} _.
Arguments file_ref_source {p} _.
Arguments file_ref_at     {p} _.
Definition FileRef := FileRef_T.

Record NodeRef_T (p : GoProgram) := mkNodeRef {
  node_ref_file  : FileRef p;
  node_ref_local : positive;
  node_ref_valid : valid_localb (file_ref_source node_ref_file) node_ref_local = true
}.
Arguments node_ref_file  {p} _.
Arguments node_ref_local {p} _.
Arguments node_ref_valid {p} _.
Definition NodeRef := NodeRef_T.

Definition node_ref_key {p} (r : NodeRef p) : NodeKey :=
  mkKey (file_ref_path (node_ref_file r)) (node_ref_local r).

Record SyntaxIndex_T (p : GoProgram) := mkSyntaxIndex {
  si_outer : OFM.t FileIndex;
  si_ok    : si_outer = outer_of (prog_files p)
}.
Arguments si_outer {p} _.
Arguments si_ok    {p} _.
Definition SyntaxIndex := SyntaxIndex_T.
Definition index_program (p : GoProgram) : SyntaxIndex p :=
  mkSyntaxIndex p (outer_of (prog_files p)) eq_refl.

Lemma si_ok_at {p} (idx : SyntaxIndex p) path f :
  OFM.find path (prog_files p) = Some f ->
  OFM.find path (si_outer idx) = Some (build_file f).
Proof. intros H. rewrite (si_ok idx). apply outer_get_at. exact H. Qed.

Definition ref_fi_opt {p} (idx : SyntaxIndex p) (r : NodeRef p) : option FileIndex :=
  OFM.find (file_ref_path (node_ref_file r)) (si_outer idx).
Lemma ref_fi_some {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  ref_fi_opt idx r = Some (build_file (file_ref_source (node_ref_file r))).
Proof. unfold ref_fi_opt. apply (si_ok_at idx). apply (file_ref_at (node_ref_file r)). Qed.
Lemma ref_fi_some' {p} (idx : SyntaxIndex p) (r : NodeRef p) : ref_fi_opt idx r <> None.
Proof. rewrite ref_fi_some. discriminate. Qed.
Definition ref_fi {p} (idx : SyntaxIndex p) (r : NodeRef p) : FileIndex :=
  option_get (ref_fi_opt idx r) (ref_fi_some' idx r).
Lemma ref_fi_eq {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  ref_fi idx r = build_file (file_ref_source (node_ref_file r)).
Proof. unfold ref_fi. apply option_get_eq, ref_fi_some. Qed.

Definition ref_meta_opt {p} (idx : SyntaxIndex p) (r : NodeRef p) : option NodeMeta :=
  NodeTable.get (node_ref_local r) (fi_table (ref_fi idx r)).
Lemma ref_meta_some {p} (idx : SyntaxIndex p) (r : NodeRef p) : ref_meta_opt idx r <> None.
Proof.
  unfold ref_meta_opt. rewrite ref_fi_eq.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))));
    [discriminate | discriminate Hv].
Qed.

Definition ref_meta {p} (idx : SyntaxIndex p) (r : NodeRef p) : NodeMeta :=
  option_get (ref_meta_opt idx r) (ref_meta_some idx r).

Lemma ref_meta_spec {p} (idx : SyntaxIndex p) (r : NodeRef p) m :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some m ->
  ref_meta idx r = m.
Proof. intros H. unfold ref_meta. apply option_get_eq. unfold ref_meta_opt. rewrite ref_fi_eq. exact H. Qed.

Definition node_kind        {p} (idx : SyntaxIndex p) (r : NodeRef p) : SyntaxKind := nm_kind (ref_meta idx r).
Definition node_role        {p} (idx : SyntaxIndex p) (r : NodeRef p) : NodeRole   := nm_role (ref_meta idx r).
Definition node_subtree_end {p} (idx : SyntaxIndex p) (r : NodeRef p) : positive   := nm_subtree_end (ref_meta idx r).
Definition containing_file {p} (r : NodeRef p) : FileRef p := node_ref_file r.

Lemma ref_meta_get {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [| discriminate Hv].
  rewrite (ref_meta_spec idx r m E). reflexivity.
Qed.

Lemma parent_valid {p} (idx : SyntaxIndex p) (r : NodeRef p) pid :
  nm_parent (ref_meta idx r) = Some pid -> valid_localb (file_ref_source (node_ref_file r)) pid = true.
Proof.
  intros Hpar.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  assert (Hne : node_ref_local r <> root_id).
  { intro Hr. rewrite Hr in Hget. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]].
    rewrite Hg in Hget. injection Hget as Heq. rewrite <- Heq in Hpar. rewrite Hp0 in Hpar. discriminate Hpar. }
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [q [mq [Hpar' [Hgq _]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  unfold valid_localb. rewrite Hgq. reflexivity.
Qed.

Definition parent_of {p} (idx : SyntaxIndex p) (r : NodeRef p) : option (NodeRef p) :=
  (match nm_parent (ref_meta idx r) as o return (nm_parent (ref_meta idx r) = o -> option (NodeRef p)) with
   | Some pid => fun H => Some (mkNodeRef p (node_ref_file r) pid (parent_valid idx r pid H))
   | None     => fun _ => None
   end) eq_refl.

Lemma child_valid (f : GoSourceFile) local c :
  In c (child_ids (fi_table (build_file f)) local) -> valid_localb f c = true.
Proof.
  intros Hin. unfold child_ids in Hin.
  destruct (NodeTable.get local (fi_table (build_file f))) as [m|] eqn:El; [|destruct Hin].
  apply child_enum_sound in Hin. unfold parent_id in Hin.
  unfold valid_localb. destruct (NodeTable.get c (fi_table (build_file f))); [reflexivity | discriminate Hin].
Qed.

Fixpoint refine_children {p} (fr : FileRef p) (ids : list positive)
  : (forall c, In c ids -> valid_localb (file_ref_source fr) c = true) -> list (NodeRef p) :=
  match ids with
  | []        => fun _    => []
  | c :: rest => fun Hall =>
      mkNodeRef p fr c (Hall c (or_introl eq_refl)) :: refine_children fr rest (fun c' H => Hall c' (or_intror H))
  end.

Lemma children_valid {p} (idx : SyntaxIndex p) (r : NodeRef p) c :
  In c (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) ->
  valid_localb (file_ref_source (node_ref_file r)) c = true.
Proof. rewrite ref_fi_eq. apply child_valid. Qed.

Definition children_of {p} (idx : SyntaxIndex p) (r : NodeRef p) : list (NodeRef p) :=
  refine_children (node_ref_file r)
    (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)) (children_valid idx r).

Definition file_of_path (p : GoProgram) (fp : FilePath) : option (FileRef p) :=
  (match OFM.find fp (prog_files p) as o
         return (OFM.find fp (prog_files p) = o -> option (FileRef p)) with
   | Some f => fun H => Some (mkFileRef p fp f H)
   | None   => fun _ => None
   end) eq_refl.

Definition valid_in_index {p} (idx : SyntaxIndex p) (fr : FileRef p) (local : positive) : bool :=
  match OFM.find (file_ref_path fr) (si_outer idx) with
  | Some fi => match NodeTable.get local (fi_table fi) with Some _ => true | None => false end
  | None    => false
  end.
Lemma valid_in_index_eq {p} (idx : SyntaxIndex p) (fr : FileRef p) (local : positive) :
  valid_in_index idx fr local = valid_localb (file_ref_source fr) local.
Proof.
  unfold valid_in_index, valid_localb.
  rewrite (si_ok_at idx (file_ref_path fr) (file_ref_source fr) (file_ref_at fr)). reflexivity.
Qed.
Lemma valid_in_index_true {p} (idx : SyntaxIndex p) (fr : FileRef p) (local : positive) :
  valid_in_index idx fr local = true -> valid_localb (file_ref_source fr) local = true.
Proof. rewrite valid_in_index_eq. exact (fun H => H). Qed.

Definition ref_of_key (p : GoProgram) (idx : SyntaxIndex p) (k : NodeKey) : option (NodeRef p) :=
  match file_of_path p (nk_file k) with
  | Some fr =>
      (match valid_in_index idx fr (nk_local k) as b
             return (valid_in_index idx fr (nk_local k) = b -> option (NodeRef p)) with
       | true  => fun H => Some (mkNodeRef p fr (nk_local k) (valid_in_index_true idx fr (nk_local k) H))
       | false => fun _ => None
       end) eq_refl
  | None => None
  end.

(* --- lift EXACT source-occurrence correspondence through the sealed reference API. --- *)

Lemma source_occ_of_ref_some {p} (r : NodeRef p) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) <> None.
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [|discriminate Hv].
  destruct (meta_source_occurrence _ _ _ E) as [o [Ho _]]. rewrite Ho. discriminate.
Qed.

Definition source_occurrence_of_ref {p} (r : NodeRef p) : SourceOccurrence :=
  option_get (source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r))
             (source_occ_of_ref_some r).

Lemma source_occ_of_ref_eq {p} (r : NodeRef p) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r)
    = Some (source_occurrence_of_ref r).
Proof. unfold source_occurrence_of_ref. apply option_get_some. Qed.

Theorem ref_meta_matches_source {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
Proof.
  pose proof (ref_meta_get idx r) as Hget.
  pose proof (build_file_source_exact (file_ref_source (node_ref_file r)) (node_ref_local r)) as HE.
  rewrite (source_occ_of_ref_eq r) in HE. cbn [option_map] in HE.
  rewrite Hget in HE. injection HE as HEq. exact HEq.
Qed.

Theorem node_kind_matches_source {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
Proof. unfold node_kind. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_role_matches_source {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  node_role idx r = occurrence_role (source_occurrence_of_ref r).
Proof. unfold node_role. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_parent_matches_source {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  nm_parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
Proof. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_subtree_end_matches_source {p} (idx : SyntaxIndex p) (r : NodeRef p) :
  node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
Proof. unfold node_subtree_end. rewrite ref_meta_matches_source. reflexivity. Qed.

Definition node_at {p} (r : NodeRef p) : option GoExpr := view_expr (source_occurrence_of_ref r).
Theorem node_at_matches_source_view {p} (r : NodeRef p) :
  node_at r = view_expr (source_occurrence_of_ref r).
Proof. reflexivity. Qed.

(* --- reference extensionality (validity + membership proofs are irrelevant). --- *)

Lemma node_ref_ext (p : GoProgram) (r1 r2 : NodeRef p) :
  node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; simpl; intros -> ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma file_ref_ext (p : GoProgram) (fr1 fr2 : FileRef p) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [p1 f1 h1], fr2 as [p2 f2 h2]; simpl; intros Hp. subst p2.
  assert (f1 = f2) by (pose proof h1 as q; rewrite h2 in q; injection q as <-; reflexivity).
  subst f2. f_equal. apply (UIP_dec option_gosourcefile_eq_dec).
Qed.

(* --- total-API correctness. --- *)

Theorem thm_node_kind (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  node_kind idx r = nm_kind (ref_meta idx r).
Proof. reflexivity. Qed.
Theorem thm_node_role (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  node_role idx r = nm_role (ref_meta idx r).
Proof. reflexivity. Qed.
Theorem thm_ref_meta_built (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
Proof. apply ref_meta_get. Qed.
Theorem thm_containing_file (p : GoProgram) (r : NodeRef p) :
  containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = nk_file (node_ref_key r).
Proof. split; reflexivity. Qed.

Lemma parent_of_none (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  nm_parent (ref_meta idx r) = None -> parent_of idx r = None.
Proof.
  intros Hn. unfold parent_of. generalize (@eq_refl (option positive) (nm_parent (ref_meta idx r))).
  destruct (nm_parent (ref_meta idx r)) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

Lemma parent_of_some (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) pid :
  nm_parent (ref_meta idx r) = Some pid ->
  exists pr, parent_of idx r = Some pr
             /\ node_ref_file pr = node_ref_file r /\ node_ref_local pr = pid.
Proof.
  intros Hs. unfold parent_of. generalize (@eq_refl (option positive) (nm_parent (ref_meta idx r))).
  destruct (nm_parent (ref_meta idx r)) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | cbn; congruence]].
  - congruence.
Qed.

Theorem thm_parent_root (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  node_ref_local r = root_id -> parent_of idx r = None.
Proof.
  intros Hr. apply parent_of_none.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. pose proof (ref_meta_get idx r) as Hget.
  rewrite Hr, Hg in Hget. injection Hget as Heq. rewrite <- Heq. exact Hp0.
Qed.

Theorem thm_parent_nonroot (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
Proof.
  intros Hne.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [q [mq [Hpar _]]].
  destruct (parent_of_some p idx r q Hpar) as [pr [Hpr _]]. exists pr. exact Hpr.
Qed.

Theorem node_parent_ref_matches_source (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  match occurrence_parent (source_occurrence_of_ref r) with
  | None     => parent_of idx r = None
  | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
  end.
Proof.
  rewrite <- (node_parent_matches_source idx r).
  destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some p idx r pid Hp) as [pr [Hpr [_ Hpl]]]. exists pr. split; [exact Hpr | exact Hpl].
  - apply (parent_of_none p idx r Hp).
Qed.

Theorem node_ref_key_inj (p : GoProgram) (r1 r2 : NodeRef p) :
  node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  intros H. unfold node_ref_key in H. injection H as Hpath Hlocal.
  apply node_ref_ext; [ apply file_ref_ext; exact Hpath | exact Hlocal ].
Qed.

Theorem thm_parent_same_file (p : GoProgram) (idx : SyntaxIndex p) (r pr : NodeRef p) :
  parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
Proof.
  intros H. destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some p idx r pid Hp) as [pr' [Hpr' [Hf _]]].
    rewrite H in Hpr'. injection Hpr' as <-. exact Hf.
  - rewrite (parent_of_none p idx r Hp) in H. discriminate H.
Qed.

Lemma refine_children_file (p : GoProgram) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> node_ref_file cr = fr.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [reflexivity | eapply IH; exact Hin].
Qed.
Theorem thm_children_same_file (p : GoProgram) (idx : SyntaxIndex p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
Proof. unfold children_of. apply refine_children_file. Qed.

Lemma refine_children_local (p : GoProgram) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> In (node_ref_local cr) ids.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.
Lemma refine_children_complete (p : GoProgram) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) c :
  In c ids -> exists cr, In cr (refine_children fr ids H) /\ node_ref_local cr = c.
Proof.
  revert H. induction ids as [|c0 rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - eexists. split; [left; reflexivity | reflexivity].
  - destruct (IH (fun c' Hc' => H c' (or_intror Hc')) Hin) as [cr [Hcr Hl]].
    exists cr. split; [right; exact Hcr | exact Hl].
Qed.

Theorem thm_children_sound (p : GoProgram) (idx : SyntaxIndex p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> In (node_ref_local cr) (child_ids (fi_table (ref_fi idx r)) (node_ref_local r)).
Proof. unfold children_of. apply refine_children_local. Qed.

Lemma refine_children_map_local (p : GoProgram) (fr : FileRef p) ids
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

Theorem thm_children_of_source_order (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
Proof.
  unfold children_of. rewrite refine_children_map_local, (ref_fi_eq idx r). apply thm11_children_sorted.
Qed.

Theorem thm_children_of_nodup (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  NoDup (children_of idx r).
Proof.
  apply (NoDup_map_inv node_ref_local). apply sorted_lt_nodup. apply thm_children_of_source_order.
Qed.

Lemma file_of_path_path (p : GoProgram) (fp : FilePath) (fr : FileRef p) :
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof.
  unfold file_of_path. generalize (@eq_refl (option GoSourceFile) (OFM.find fp (prog_files p))).
  destruct (OFM.find fp (prog_files p)) as [f|] at 2 3; intros e H; [| discriminate H].
  injection H as <-. reflexivity.
Qed.

Theorem ref_of_key_sound (p : GoProgram) (idx : SyntaxIndex p) (k : NodeKey) (r : NodeRef p) :
  ref_of_key p idx k = Some r -> node_ref_key r = k.
Proof.
  unfold ref_of_key. destruct (file_of_path p (nk_file k)) as [fr|] eqn:Ef; [| discriminate].
  generalize (@eq_refl bool (valid_in_index idx fr (nk_local k))).
  destruct (valid_in_index idx fr (nk_local k)) at 2 3; intros e H; [| discriminate H].
  injection H as <-. unfold node_ref_key. simpl.
  rewrite (file_of_path_path p (nk_file k) fr Ef). destruct k; reflexivity.
Qed.

Lemma file_of_path_complete (p : GoProgram) (fr : FileRef p) :
  file_of_path p (file_ref_path fr) = Some fr.
Proof.
  unfold file_of_path.
  generalize (@eq_refl (option GoSourceFile) (OFM.find (file_ref_path fr) (prog_files p))).
  destruct (OFM.find (file_ref_path fr) (prog_files p)) as [f|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - exfalso. rewrite (file_ref_at fr) in e. discriminate e.
Qed.

Theorem ref_of_key_complete (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  ref_of_key p idx (node_ref_key r) = Some r.
Proof.
  unfold ref_of_key, node_ref_key. cbn [nk_file nk_local].
  rewrite (file_of_path_complete p (node_ref_file r)).
  generalize (@eq_refl bool (valid_in_index idx (node_ref_file r) (node_ref_local r))).
  destruct (valid_in_index idx (node_ref_file r) (node_ref_local r)) at 2 3; intros e.
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. rewrite valid_in_index_eq, (node_ref_valid r) in e. discriminate e.
Qed.

Theorem file_of_path_source (p : GoProgram) (path : FilePath) (f : GoSourceFile) :
  find_file path (prog_files p) = Some f ->
  exists fr, file_of_path p path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
Proof.
  intros Hfind. exists (mkFileRef p path f Hfind). split; [| split; reflexivity].
  unfold file_of_path.
  generalize (@eq_refl (option GoSourceFile) (OFM.find path (prog_files p))).
  destruct (OFM.find path (prog_files p)) as [f'|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - unfold find_file in Hfind. rewrite Hfind in e. discriminate e.
Qed.

Theorem ref_of_key_source (p : GoProgram) (idx : SyntaxIndex p) (path : FilePath) (f : GoSourceFile) (local : positive) :
  find_file path (prog_files p) = Some f -> valid_localb f local = true ->
  exists r, ref_of_key p idx (mkKey path local) = Some r
            /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
Proof.
  intros Hfind Hv.
  destruct (file_of_path_source p path f Hfind) as [fr [Hfp [_ Hff]]].
  assert (Hvi : valid_in_index idx fr local = true) by (rewrite valid_in_index_eq, Hff; exact Hv).
  unfold ref_of_key. cbn [nk_file nk_local]. rewrite Hfp.
  generalize (@eq_refl bool (valid_in_index idx fr local)).
  destruct (valid_in_index idx fr local) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | exact Hff]].
  - rewrite Hvi in e. discriminate e.
Qed.

Theorem file_ref_path_inj (p : GoProgram) (fr1 fr2 : FileRef p) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof. apply file_ref_ext. Qed.

Theorem thm_child_parent (p : GoProgram) (idx : SyntaxIndex p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> parent_of idx cr = Some r.
Proof.
  intros Hin.
  pose proof (thm_children_same_file p idx r cr Hin) as Hf.
  pose proof (thm_children_sound p idx r cr Hin) as Hsound.
  apply child_ids_parent in Hsound.
  pose proof (ref_meta_get idx cr) as Hget.
  rewrite Hf in Hget. rewrite <- (ref_fi_eq idx r) in Hget.
  unfold parent_id in Hsound. rewrite Hget in Hsound.
  destruct (parent_of_some p idx cr (node_ref_local r) Hsound) as [pr [Hpr [Hpf Hpl]]].
  rewrite Hpr. f_equal. apply node_ref_ext; [ rewrite Hpf; exact Hf | exact Hpl ].
Qed.

Theorem thm_parent_child (p : GoProgram) (idx : SyntaxIndex p) (r pr : NodeRef p) :
  parent_of idx r = Some pr -> In r (children_of idx pr).
Proof.
  intros Hpar.
  pose proof (thm_parent_same_file p idx r pr Hpar) as Hf.
  assert (Hp' : nm_parent (ref_meta idx r) = Some (node_ref_local pr)).
  { destruct (nm_parent (ref_meta idx r)) as [pid|] eqn:Hnp.
    - destruct (parent_of_some p idx r pid Hnp) as [pr' [Hpr' [_ Hpl]]].
      rewrite Hpar in Hpr'. injection Hpr' as <-. rewrite Hpl. reflexivity.
    - rewrite (parent_of_none p idx r Hnp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx r) as Hgetr. rewrite <- Hf in Hgetr.
  pose proof (thm4_parent_has_child (file_ref_source (node_ref_file pr))
                (node_ref_local pr) (node_ref_local r) (ref_meta idx r) Hgetr Hp') as Hchild.
  rewrite <- (ref_fi_eq idx pr) in Hchild.
  destruct (refine_children_complete p (node_ref_file pr)
              (child_ids (fi_table (ref_fi idx pr)) (node_ref_local pr))
              (children_valid idx pr) (node_ref_local r) Hchild) as [cr [Hcr Hcl]].
  pose proof (refine_children_file p (node_ref_file pr) _ (children_valid idx pr) cr Hcr) as Hcrf.
  assert (Hcreq : cr = r).
  { apply node_ref_ext; [ rewrite Hcrf, Hf; reflexivity | rewrite Hcl; reflexivity ]. }
  subst cr. unfold children_of. exact Hcr.
Qed.

(* --- NodeRef-level ancestry: the O(1) interval test, certified through the sealed API. --- *)

Lemma ref_fi_table_same_file (p : GoProgram) (idx : SyntaxIndex p) (x y : NodeRef p) :
  node_ref_file x = node_ref_file y -> fi_table (ref_fi idx x) = fi_table (ref_fi idx y).
Proof. intros H. rewrite (ref_fi_eq idx x), (ref_fi_eq idx y), H. reflexivity. Qed.

Lemma parentof_to_parentid (p : GoProgram) (idx : SyntaxIndex p) (d a : NodeRef p) :
  parent_of idx d = Some a ->
  node_ref_file a = node_ref_file d /\
  parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some (node_ref_local a).
Proof.
  intros Hpar. pose proof (thm_parent_same_file p idx d a Hpar) as Hf. split; [exact Hf|].
  assert (Hnp : nm_parent (ref_meta idx d) = Some (node_ref_local a)).
  { destruct (nm_parent (ref_meta idx d)) as [pid|] eqn:Hp.
    - destruct (parent_of_some p idx d pid Hp) as [a' [Ha' [_ Hal]]].
      rewrite Hpar in Ha'. injection Ha' as <-. rewrite Hal. reflexivity.
    - rewrite (parent_of_none p idx d Hp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_fi_eq idx d) in Hget.
  unfold parent_id. rewrite Hget. exact Hnp.
Qed.

Lemma parentid_to_parentof (p : GoProgram) (idx : SyntaxIndex p) (d : NodeRef p) pa :
  parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some pa ->
  exists a, parent_of idx d = Some a /\ node_ref_local a = pa /\ node_ref_file a = node_ref_file d.
Proof.
  intros Hpid.
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_fi_eq idx d) in Hget.
  unfold parent_id in Hpid. rewrite Hget in Hpid.
  destruct (parent_of_some p idx d pa Hpid) as [a [Ha [Hf Hal]]].
  exists a. split; [exact Ha | split; [exact Hal | exact Hf]].
Qed.

Inductive RefAncestor (p : GoProgram) (idx : SyntaxIndex p) : NodeRef p -> NodeRef p -> Prop :=
| RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor p idx a d
| RAnc_step : forall a q d, RefAncestor p idx a q -> parent_of idx d = Some q -> RefAncestor p idx a d.

Lemma refanc_same_file (p : GoProgram) (idx : SyntaxIndex p) (a d : NodeRef p) :
  RefAncestor p idx a d -> node_ref_file a = node_ref_file d.
Proof.
  intros H. induction H as [a d Hpar | a q d Hanc IH Hpar].
  - apply (proj1 (parentof_to_parentid p idx d a Hpar)).
  - rewrite IH. apply (proj1 (parentof_to_parentid p idx d q Hpar)).
Qed.

Lemma refanc_to_anc (p : GoProgram) (idx : SyntaxIndex p) (a d : NodeRef p) :
  RefAncestor p idx a d -> Ancestor (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local d).
Proof.
  intros H. induction H as [a d Hpar | a q d Hanc IH Hpar].
  - apply Anc_dir. apply (proj2 (parentof_to_parentid p idx d a Hpar)).
  - pose proof (proj1 (parentof_to_parentid p idx d q Hpar)) as Hf.
    rewrite (ref_fi_table_same_file p idx q d Hf) in IH.
    apply (Anc_step (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local q) (node_ref_local d) IH).
    apply (proj2 (parentof_to_parentid p idx d q Hpar)).
Qed.

Lemma anc_to_refanc_aux (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) (al dl : positive)
  (Hanc : Ancestor (fi_table (build_file (file_ref_source fr))) al dl) :
  forall (d : NodeRef p), node_ref_file d = fr -> node_ref_local d = dl ->
  exists a, node_ref_file a = fr /\ node_ref_local a = al /\ RefAncestor p idx a d.
Proof.
  induction Hanc as [al dl Hpid | al pl dl Hanc_ap IH Hpid_d]; intros d Hdf Hdl.
  - assert (Hpd : parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some al)
      by (rewrite (ref_fi_eq idx d), Hdf, Hdl; exact Hpid).
    destruct (parentid_to_parentof p idx d al Hpd) as [a [Ha [Hal Haf]]].
    exists a. split; [rewrite Haf; exact Hdf | split; [exact Hal | apply RAnc_dir; exact Ha]].
  - assert (Hpd : parent_id (fi_table (ref_fi idx d)) (node_ref_local d) = Some pl)
      by (rewrite (ref_fi_eq idx d), Hdf, Hdl; exact Hpid_d).
    destruct (parentid_to_parentof p idx d pl Hpd) as [pr [Hp [Hpl Hpf]]].
    destruct (IH pr (eq_trans Hpf Hdf) Hpl) as [a [Haf [Hal Hra]]].
    exists a. split; [exact Haf | split; [exact Hal | apply (RAnc_step p idx a pr d Hra Hp)]].
Qed.

Lemma anc_to_refanc (p : GoProgram) (idx : SyntaxIndex p) (a d : NodeRef p) :
  node_ref_file a = node_ref_file d ->
  Ancestor (fi_table (build_file (file_ref_source (node_ref_file d)))) (node_ref_local a) (node_ref_local d) ->
  RefAncestor p idx a d.
Proof.
  intros Hf Hanc.
  destruct (anc_to_refanc_aux p idx (node_ref_file d) (node_ref_local a) (node_ref_local d) Hanc d eq_refl eq_refl)
    as [a' [Haf [Hal Hra]]].
  assert (a' = a) by (apply node_ref_ext; [ rewrite Haf; symmetry; exact Hf | exact Hal ]).
  subst a'. exact Hra.
Qed.

Definition is_ancestor_ref {p} (idx : SyntaxIndex p) (a d : NodeRef p) : bool :=
  fp_eqb (file_ref_path (node_ref_file a)) (file_ref_path (node_ref_file d)) &&
  is_ancestor_local (fi_table (ref_fi idx d)) (node_ref_local a) (node_ref_local d).

Lemma ref_local_present (p : GoProgram) (idx : SyntaxIndex p) (a d : NodeRef p) :
  node_ref_file a = node_ref_file d ->
  NodeTable.get (node_ref_local a) (fi_table (build_file (file_ref_source (node_ref_file d)))) <> None.
Proof.
  intros Hf. rewrite <- Hf. pose proof (ref_meta_get idx a) as Hg. rewrite Hg. discriminate.
Qed.

Theorem thm_ref_ancestry (p : GoProgram) (idx : SyntaxIndex p) (a d : NodeRef p) :
  is_ancestor_ref idx a d = true <-> RefAncestor p idx a d.
Proof.
  unfold is_ancestor_ref. split.
  - intros Hb. apply andb_true_iff in Hb as [Hpath Hloc]. apply fp_eqb_eq in Hpath.
    assert (Hf : node_ref_file a = node_ref_file d) by (apply file_ref_ext; exact Hpath).
    apply (anc_to_refanc p idx a d Hf).
    rewrite (ref_fi_eq idx d) in Hloc.
    apply (proj1 (thm13_interval_ancestry (file_ref_source (node_ref_file d))
                    (node_ref_local a) (node_ref_local d) (ref_local_present p idx a d Hf))).
    exact Hloc.
  - intros Hra.
    pose proof (refanc_same_file p idx a d Hra) as Hf.
    pose proof (refanc_to_anc p idx a d Hra) as Hanc.
    apply andb_true_iff. split.
    + apply fp_eqb_eq. rewrite Hf. reflexivity.
    + rewrite (ref_fi_eq idx d). rewrite (ref_fi_eq idx d) in Hanc.
      apply (proj2 (thm13_interval_ancestry (file_ref_source (node_ref_file d))
                      (node_ref_local a) (node_ref_local d) (ref_local_present p idx a d Hf))).
      exact Hanc.
Qed.

(* --- minting soundness for FileRef + the rejection cases. --- *)

Theorem file_of_path_sound (p : GoProgram) (fp : FilePath) (fr : FileRef p) :
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof. apply file_of_path_path. Qed.

(* the SOURCE a minted FileRef carries is EXACTLY the program's map binding at the queried path. *)
Theorem file_of_path_source_exact (p : GoProgram) (fp : FilePath) (fr : FileRef p) :
  file_of_path p fp = Some fr -> find_file fp (prog_files p) = Some (file_ref_source fr).
Proof.
  intros H. pose proof (file_of_path_path p fp fr H) as Hpath.
  pose proof (file_ref_at fr) as Hat. rewrite Hpath in Hat. exact Hat.
Qed.

Lemma file_of_path_none (p : GoProgram) (fp : FilePath) :
  OFM.find fp (prog_files p) = None -> file_of_path p fp = None.
Proof.
  intros H. unfold file_of_path.
  generalize (@eq_refl (option GoSourceFile) (OFM.find fp (prog_files p))).
  destruct (OFM.find fp (prog_files p)) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

Theorem ref_of_key_invalid_path (p : GoProgram) (idx : SyntaxIndex p) (fp : FilePath) (local : positive) :
  find_file fp (prog_files p) = None -> ref_of_key p idx (mkKey fp local) = None.
Proof.
  intros H. unfold ref_of_key. cbn [nk_file nk_local].
  rewrite (file_of_path_none p fp H). reflexivity.
Qed.

Theorem ref_of_key_invalid_local (p : GoProgram) (idx : SyntaxIndex p) (fp : FilePath) (f : GoSourceFile) (local : positive) :
  find_file fp (prog_files p) = Some f -> valid_localb f local = false -> ref_of_key p idx (mkKey fp local) = None.
Proof.
  intros Hf Hv. destruct (file_of_path_source p fp f Hf) as [fr [Hfp [_ Hfs]]].
  assert (Hvi : valid_in_index idx fr local = false) by (rewrite valid_in_index_eq, Hfs; exact Hv).
  unfold ref_of_key. cbn [nk_file nk_local]. rewrite Hfp.
  generalize (@eq_refl bool (valid_in_index idx fr local)).
  destruct (valid_in_index idx fr local) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

(* --- decidable NodeRef equality: reference identity IS NodeKey identity. --- *)

Definition noderef_eq_dec {p} (r1 r2 : NodeRef p) : {r1 = r2} + {r1 <> r2}.
Proof.
  destruct (thm8_nodekey_eq_dec (node_ref_key r1) (node_ref_key r2)) as [Heq|Hne].
  - left. apply node_ref_key_inj. exact Heq.
  - right. intro H. apply Hne. rewrite H. reflexivity.
Defined.

(* --- the file-root reference + the canonical preorder enumeration of ALL a file's references. --- *)

Definition file_root_ref {p} (fr : FileRef p) : NodeRef p :=
  mkNodeRef p fr root_id (root_valid (file_ref_source fr)).
Lemma file_root_ref_local (p : GoProgram) (fr : FileRef p) : node_ref_local (file_root_ref fr) = root_id.
Proof. reflexivity. Qed.
Lemma file_root_ref_file (p : GoProgram) (fr : FileRef p) : node_ref_file (file_root_ref fr) = fr.
Proof. reflexivity. Qed.

(* the FileRef-level index accessor: ONE outer-map lookup into the PRECOMPUTED [si_outer idx] — it REUSES the
   passed SyntaxIndex and does NOT rebuild [build_file].  Provably equal to the file's build for the proofs. *)
Definition fr_fi_opt {p} (idx : SyntaxIndex p) (fr : FileRef p) : option FileIndex :=
  OFM.find (file_ref_path fr) (si_outer idx).
Lemma fr_fi_some {p} (idx : SyntaxIndex p) (fr : FileRef p) :
  fr_fi_opt idx fr = Some (build_file (file_ref_source fr)).
Proof. unfold fr_fi_opt. apply (si_ok_at idx). apply (file_ref_at fr). Qed.
Lemma fr_fi_some' {p} (idx : SyntaxIndex p) (fr : FileRef p) : fr_fi_opt idx fr <> None.
Proof. rewrite fr_fi_some. discriminate. Qed.
Definition fr_fi {p} (idx : SyntaxIndex p) (fr : FileRef p) : FileIndex :=
  option_get (fr_fi_opt idx fr) (fr_fi_some' idx fr).
Lemma fr_fi_eq {p} (idx : SyntaxIndex p) (fr : FileRef p) : fr_fi idx fr = build_file (file_ref_source fr).
Proof. unfold fr_fi. apply option_get_eq, fr_fi_some. Qed.

Lemma all_ids_valid_idx {p} (idx : SyntaxIndex p) (fr : FileRef p) :
  forall c, In c (all_ids (fr_fi idx fr)) -> valid_localb (file_ref_source fr) c = true.
Proof. rewrite (fr_fi_eq idx fr). apply all_ids_valid. Qed.

(* the canonical preorder enumeration of ALL a file's references, reusing the precomputed FileIndex. *)
Definition file_refs {p} (idx : SyntaxIndex p) (fr : FileRef p) : list (NodeRef p) :=
  refine_children fr (all_ids (fr_fi idx fr)) (all_ids_valid_idx idx fr).

Theorem file_refs_same_file (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p) :
  In r (file_refs idx fr) -> node_ref_file r = fr.
Proof. unfold file_refs. apply refine_children_file. Qed.

Lemma file_refs_map_local (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) :
  map node_ref_local (file_refs idx fr) = all_ids (fr_fi idx fr).
Proof. unfold file_refs. apply refine_children_map_local. Qed.

Theorem file_refs_complete (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p) :
  node_ref_file r = fr -> In r (file_refs idx fr).
Proof.
  intros Hf. pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv. rewrite Hf in Hv.
  destruct (NodeTable.get (node_ref_local r) (fi_table (build_file (file_ref_source fr)))) as [m|] eqn:E;
    [|discriminate Hv].
  pose proof (thm7_enum_complete (file_ref_source fr) (node_ref_local r) m E) as Hin.
  rewrite <- (fr_fi_eq idx fr) in Hin.
  destruct (refine_children_complete p fr (all_ids (fr_fi idx fr))
              (all_ids_valid_idx idx fr) (node_ref_local r) Hin) as [cr [Hcr Hcl]].
  assert (Hcreq : cr = r).
  { apply node_ref_ext;
      [ rewrite (refine_children_file p fr _ (all_ids_valid_idx idx fr) cr Hcr), Hf; reflexivity
      | rewrite Hcl; reflexivity ]. }
  subst cr. exact Hcr.
Qed.

Theorem file_refs_nodup (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) : NoDup (file_refs idx fr).
Proof.
  apply (NoDup_map_inv node_ref_local). rewrite file_refs_map_local, (fr_fi_eq idx fr). apply pos_seq_NoDup.
Qed.

Theorem file_refs_source_order (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) :
  StronglySorted Pos.lt (map node_ref_local (file_refs idx fr)).
Proof. rewrite file_refs_map_local, (fr_fi_eq idx fr). apply pos_seq_sorted. Qed.

Theorem file_root_ref_in_refs (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) :
  In (file_root_ref fr) (file_refs idx fr).
Proof. apply file_refs_complete. reflexivity. Qed.

(* every occurrence is reachable from its file root by repeated parent links (the root is a strict ancestor
   of every non-root occurrence — the root's subtree is the whole file). *)
Theorem thm_reachable_from_root (p : GoProgram) (idx : SyntaxIndex p) (r : NodeRef p) :
  node_ref_local r <> root_id -> RefAncestor p idx (file_root_ref (node_ref_file r)) r.
Proof.
  intros Hne. apply anc_to_refanc; [ reflexivity | ].
  cbn [node_ref_local file_root_ref].
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_root WF) as [m0 [Hgr [_ Hend]]].
  apply (sub_snd WF root_id (node_ref_local r) m0);
    [ lia | lia | exact Hgr | lia | rewrite Hend; exact Hhi ].
Qed.

(* every ENUMERATED reference is the file root or reachable from it — the enumeration is a rooted tree. *)
Theorem thm_refs_reachable (p : GoProgram) (idx : SyntaxIndex p) (fr : FileRef p) (r : NodeRef p) :
  In r (file_refs idx fr) -> r = file_root_ref fr \/ RefAncestor p idx (file_root_ref fr) r.
Proof.
  intros Hin. pose proof (file_refs_same_file p idx fr r Hin) as Hf.
  destruct (Pos.eq_dec (node_ref_local r) root_id) as [Hroot|Hnroot].
  - left. apply node_ref_ext; [ rewrite Hf; reflexivity | rewrite Hroot; reflexivity ].
  - right. rewrite <- Hf. apply thm_reachable_from_root. exact Hnroot.
Qed.

End Snap.

(* negative ABSTRACTION checks: the raw index map and raw record constructors are NOT reachable through the
   sealed [Snap] interface (each [Check] FAILS, so [Fail Check] succeeds). *)
Fail Check Snap.mkSyntaxIndex.
Fail Check Snap.mkFileRef.
Fail Check Snap.mkNodeRef.
Fail Check Snap.si_outer.
Fail Check Snap.ref_fi.
Fail Check Snap.fr_fi.

(* ================================================================================================= *)
(** ** §13 — typed / kind-refined references.  A [NodeRefOf p k] is a [NodeRef p] whose EXACT source        *)
(*    occurrence has kind [k] — the kind proof is tied to [source_occurrence_of_ref] (via                   *)
(*    [node_kind_matches_source]), NOT an author-supplied boolean.  Erasure recovers the underlying ref;    *)
(*    the erased NodeKey determines the typed-ref identity (no second identity system).                     *)
(* ================================================================================================= *)

Definition NodeRefOf (p : GoProgram) (k : SyntaxKind) : Type :=
  { r : Snap.NodeRef p | occurrence_kind (Snap.source_occurrence_of_ref r) = k }.
Definition erase_ref {p k} (tr : NodeRefOf p k) : Snap.NodeRef p := proj1_sig tr.
Definition FileNodeRef      (p : GoProgram) := NodeRefOf p KFile.
Definition PackageClauseRef (p : GoProgram) := NodeRefOf p KPackageClause.
Definition DeclRef          (p : GoProgram) := NodeRefOf p KTopLevelDecl.
Definition StmtRef          (p : GoProgram) := NodeRefOf p KStatement.
Definition ExprRef          (p : GoProgram) := NodeRefOf p KExpression.

Definition syntaxkind_eq_dec (a b : SyntaxKind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* the generic kind-refiner: refine a reference to kind [k] iff its source occurrence has kind [k] — the
   kind proof comes from [node_kind_matches_source], so it cannot be forged. *)
Definition as_kind {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) (k : SyntaxKind) : option (NodeRefOf p k) :=
  match syntaxkind_eq_dec (Snap.node_kind idx r) k with
  | left H  => Some (exist _ r (eq_trans (eq_sym (Snap.node_kind_matches_source p idx r)) H))
  | right _ => None
  end.
Definition as_file_node {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) : option (FileNodeRef p) := as_kind idx r KFile.
Definition as_package_clause {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) : option (PackageClauseRef p) := as_kind idx r KPackageClause.
Definition as_decl {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) : option (DeclRef p) := as_kind idx r KTopLevelDecl.
Definition as_stmt {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) : option (StmtRef p) := as_kind idx r KStatement.
Definition as_expr {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) : option (ExprRef p) := as_kind idx r KExpression.

(* refinement soundness: erasure recovers exactly the refined reference. *)
Lemma erase_as_kind {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) (k : SyntaxKind) (tr : NodeRefOf p k) :
  as_kind idx r k = Some tr -> erase_ref tr = r.
Proof.
  unfold as_kind. destruct (syntaxkind_eq_dec (Snap.node_kind idx r) k); [|discriminate].
  intros H; injection H as <-. reflexivity.
Qed.
(* refinement completeness: a reference whose kind matches refines (and erases back to itself). *)
Lemma as_kind_complete {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) (k : SyntaxKind) :
  Snap.node_kind idx r = k -> exists tr, as_kind idx r k = Some tr /\ erase_ref tr = r.
Proof.
  intros H. unfold as_kind. destruct (syntaxkind_eq_dec (Snap.node_kind idx r) k) as [Heq|Hne]; [|contradiction].
  eexists. split; reflexivity.
Qed.
(* mismatch rejects — no fallback. *)
Lemma as_kind_mismatch {p} (idx : Snap.SyntaxIndex p) (r : Snap.NodeRef p) (k : SyntaxKind) :
  Snap.node_kind idx r <> k -> as_kind idx r k = None.
Proof.
  intros H. unfold as_kind. destruct (syntaxkind_eq_dec (Snap.node_kind idx r) k); [contradiction|reflexivity].
Qed.
(* the refined kind IS the exact source occurrence's kind (tied to the source, not free). *)
Lemma noderefof_kind {p k} (tr : NodeRefOf p k) :
  occurrence_kind (Snap.source_occurrence_of_ref (erase_ref tr)) = k.
Proof. destruct tr as [r Hk]. exact Hk. Qed.
(* erased NodeKey determines typed-reference identity — no new identity system. *)
Lemma noderefof_key_inj {p k} (tr1 tr2 : NodeRefOf p k) :
  Snap.node_ref_key (erase_ref tr1) = Snap.node_ref_key (erase_ref tr2) -> tr1 = tr2.
Proof.
  intros H. destruct tr1 as [r1 H1], tr2 as [r2 H2]. cbn [erase_ref proj1_sig] in *.
  assert (r1 = r2) by (apply Snap.node_ref_key_inj; exact H). subst r2.
  f_equal. apply (UIP_dec syntaxkind_eq_dec).
Qed.

(* ================================================================================================= *)
(** ** §21/§22 — snapshot-locality + mutation-sensitive regressions over the REAL grammar.               *)
(* ================================================================================================= *)

Definition fp_main : FilePath := mkFP "main.go"%string eq_refl.
Definition ms_gen : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated"%string eq_refl) Go1_23.
Definition ms_com : ModuleSpec := mkModuleSpec (mkMP "fido.local/common"%string eq_refl) Go1_23.

(* --- helper: recover a minted reference's exact source occurrence by computing the source spec. --- *)
Lemma soor_compute {p} (r : Snap.NodeRef p) (f : GoSourceFile) (local : positive) (occ0 : SourceOccurrence) :
  Snap.file_ref_source (Snap.node_ref_file r) = f -> Snap.node_ref_local r = local ->
  source_occurrence_at f local = Some occ0 ->
  Snap.source_occurrence_of_ref r = occ0.
Proof.
  intros Hf Hl Hs. pose proof (Snap.source_occ_of_ref_eq r) as He.
  rewrite Hf, Hl, Hs in He. injection He as <-. reflexivity.
Qed.

(* ---------- §21.3 REQUIRED: println(1, 1) — two structurally EQUAL args are DISTINCT occurrences. ---------- *)
(* preorder ids: 1 file / 2 package / 3 decl / 4 stmt / 5 arg0 (EInt 1) / 6 arg1 (EInt 1). *)
Definition sf11 : GoSourceFile := main_source [ DMain [ SPrintln [ EInt 1%N ; EInt 1%N ] ] ].
Definition prog11 : GoProgram := singleton_program ms_gen fp_main [ DMain [ SPrintln [ EInt 1%N ; EInt 1%N ] ] ].

Lemma find11 : find_file fp_main (prog_files prog11) = Some sf11.
Proof. unfold find_file, prog11, sf11, singleton_program, prog_files. apply Collections.FileMapFacts.add_eq_o. reflexivity. Qed.
(* validity is proved through the source spec: NodeTable is SEALED, so [valid_localb] cannot be computed
   directly; [build_file_source_exact] replaces the opaque [NodeTable.get] with the computable table-free
   [source_occurrence_at]. *)
Ltac valid_via_source := unfold valid_localb; rewrite build_file_source_exact; vm_compute; reflexivity.
Lemma valid11_5 : valid_localb sf11 5%positive = true. Proof. valid_via_source. Qed.
Lemma valid11_6 : valid_localb sf11 6%positive = true. Proof. valid_via_source. Qed.
Lemma src11_5 : source_occurrence_at sf11 5%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 1%N)) (Some 4%positive) (RPrintlnArg 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Lemma src11_6 : source_occurrence_at sf11 6%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 1%N)) (Some 4%positive) (RPrintlnArg 1) 6%positive).
Proof. vm_compute. reflexivity. Qed.

(* the two args, minted as validated ExprRefs through the sealed key-minting boundary. *)
Theorem reg_println_1_1 :
  exists (r5 r6 : Snap.NodeRef prog11),
    Snap.ref_of_key prog11 (Snap.index_program prog11) (mkKey fp_main 5%positive) = Some r5 /\
    Snap.ref_of_key prog11 (Snap.index_program prog11) (mkKey fp_main 6%positive) = Some r6 /\
    (* both source fragments are EQUAL... *)
    Snap.node_at r5 = Some (EInt 1%N) /\ Snap.node_at r6 = Some (EInt 1%N) /\
    (* ...yet the two references are DISTINCT (distinct keys / local ids), NOT deduplicated... *)
    r5 <> r6 /\
    Snap.node_ref_key r5 = mkKey fp_main 5%positive /\ Snap.node_ref_key r6 = mkKey fp_main 6%positive /\
    (* ...with the correct per-argument role. *)
    Snap.node_role (Snap.index_program prog11) r5 = RPrintlnArg 0 /\
    Snap.node_role (Snap.index_program prog11) r6 = RPrintlnArg 1.
Proof.
  destruct (Snap.ref_of_key_source prog11 (Snap.index_program prog11) fp_main sf11 5%positive find11 valid11_5)
    as [r5 [Hk5 [Hl5 Hf5]]].
  destruct (Snap.ref_of_key_source prog11 (Snap.index_program prog11) fp_main sf11 6%positive find11 valid11_6)
    as [r6 [Hk6 [Hl6 Hf6]]].
  pose proof (soor_compute r5 sf11 5%positive _ Hf5 Hl5 src11_5) as Ho5.
  pose proof (soor_compute r6 sf11 6%positive _ Hf6 Hl6 src11_6) as Ho6.
  pose proof (Snap.ref_of_key_sound prog11 (Snap.index_program prog11) (mkKey fp_main 5%positive) r5 Hk5) as Hkey5.
  pose proof (Snap.ref_of_key_sound prog11 (Snap.index_program prog11) (mkKey fp_main 6%positive) r6 Hk6) as Hkey6.
  exists r5, r6. repeat split; try assumption.
  - rewrite (Snap.node_at_matches_source_view r5), Ho5. reflexivity.
  - rewrite (Snap.node_at_matches_source_view r6), Ho6. reflexivity.
  - intro Hbad. rewrite Hbad, Hkey6 in Hkey5. injection Hkey5 as Hkey5. discriminate Hkey5.
  - rewrite (Snap.node_role_matches_source prog11 (Snap.index_program prog11) r5), Ho5. reflexivity.
  - rewrite (Snap.node_role_matches_source prog11 (Snap.index_program prog11) r6), Ho6. reflexivity.
Qed.

(* ---------- §21.1 — same path + shape, DIFFERENT payload => non-interchangeable ref TYPES + per-snapshot
   payload recovery; erased index DATA is extensionally equal (metadata discards the payload). ---------- *)
Definition prog_a : GoProgram := singleton_program ms_gen fp_main [ DMain [ SPrintln [ EInt 5%N ] ] ].
Definition prog_b : GoProgram := singleton_program ms_gen fp_main [ DMain [ SPrintln [ EInt 6%N ] ] ].
Definition sf_a : GoSourceFile := main_source [ DMain [ SPrintln [ EInt 5%N ] ] ].
Definition sf_b : GoSourceFile := main_source [ DMain [ SPrintln [ EInt 6%N ] ] ].

Lemma find_a : find_file fp_main (prog_files prog_a) = Some sf_a.
Proof. unfold find_file, prog_a, sf_a, singleton_program, prog_files. apply Collections.FileMapFacts.add_eq_o. reflexivity. Qed.
Lemma find_b : find_file fp_main (prog_files prog_b) = Some sf_b.
Proof. unfold find_file, prog_b, sf_b, singleton_program, prog_files. apply Collections.FileMapFacts.add_eq_o. reflexivity. Qed.
Lemma valid_a5 : valid_localb sf_a 5%positive = true. Proof. valid_via_source. Qed.
Lemma valid_b5 : valid_localb sf_b 5%positive = true. Proof. valid_via_source. Qed.
Lemma src_a5 : source_occurrence_at sf_a 5%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 5%N)) (Some 4%positive) (RPrintlnArg 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Lemma src_b5 : source_occurrence_at sf_b 5%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 6%N)) (Some 4%positive) (RPrintlnArg 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.

(* the SAME NodeKey recovers each snapshot's OWN payload: EInt 5 in prog_a, EInt 6 in prog_b. *)
Theorem reg_payload_a : exists r, Snap.ref_of_key prog_a (Snap.index_program prog_a) (mkKey fp_main 5%positive) = Some r
                                  /\ Snap.node_at r = Some (EInt 5%N).
Proof.
  destruct (Snap.ref_of_key_source prog_a (Snap.index_program prog_a) fp_main sf_a 5%positive find_a valid_a5)
    as [r [Hk [Hl Hf]]].
  exists r. split; [exact Hk|].
  rewrite (Snap.node_at_matches_source_view r), (soor_compute r sf_a 5%positive _ Hf Hl src_a5). reflexivity.
Qed.
Theorem reg_payload_b : exists r, Snap.ref_of_key prog_b (Snap.index_program prog_b) (mkKey fp_main 5%positive) = Some r
                                  /\ Snap.node_at r = Some (EInt 6%N).
Proof.
  destruct (Snap.ref_of_key_source prog_b (Snap.index_program prog_b) fp_main sf_b 5%positive find_b valid_b5)
    as [r [Hk [Hl Hf]]].
  exists r. split; [exact Hk|].
  rewrite (Snap.node_at_matches_source_view r), (soor_compute r sf_b 5%positive _ Hf Hl src_b5). reflexivity.
Qed.

(* §21.1 non-interchangeability at the TYPE level: a reference of [prog_a] is NOT a reference of [prog_b]. *)
Fail Definition reg_cross_snapshot (r : Snap.NodeRef prog_a) : Snap.NodeRef prog_b := r.

(* the ERASED index data is extensionally equal — the metadata builder discards the leaf payload (5 vs 6),
   so [outer_of] of the two snapshots are [FileMap.Equal]; only the [GoProgram] distinguishes the ref TYPES. *)
Theorem reg_index_data_equal : OFM.Equal (outer_of (prog_files prog_a)) (outer_of (prog_files prog_b)).
Proof.
  intro k. unfold outer_of, prog_a, prog_b, singleton_program, prog_files.
  rewrite !OFMF.map_o, !OFMF.add_o.
  destruct (Collections.FilePath_OT.eq_dec fp_main k) as [Heq|Hne].
  - cbn [option_map]. reflexivity.
  - rewrite !OFMF.empty_o. reflexivity.
Qed.

(* ---------- §21.2 — same FILE MAP, DIFFERENT ModuleSpec => non-interchangeable ref TYPES even though the
   erased index data is IDENTICAL: references are indexed by the exact [GoProgram], not by index data. ---------- *)
Definition prog_gen : GoProgram := singleton_program ms_gen fp_main [ DMain [ SPrintln [ EInt 5%N ] ] ].
Definition prog_com : GoProgram := singleton_program ms_com fp_main [ DMain [ SPrintln [ EInt 5%N ] ] ].
(* their file maps are identical, hence their outer index maps are equal... *)
Theorem reg_module_index_equal : OFM.Equal (outer_of (prog_files prog_gen)) (outer_of (prog_files prog_com)).
Proof. intro k. reflexivity. Qed.
(* ...yet a reference of one is NOT a reference of the other (distinct GoProgram snapshots). *)
Fail Definition reg_cross_module (r : Snap.NodeRef prog_gen) : Snap.NodeRef prog_com := r.

(* ---------- §22 — a compact, structurally rich mutation-sensitive fixture.  Preorder ids 1..13:
   1 file / 2 package / 3 decl0 / 4 stmt0 / 5 arg0 (EInt 1) / 6 arg1 (EInt 1) / 7 stmt1 / 8 arg (EBool true)
   / 9 decl1 / 10 stmt0 / 11 arg0 = outer conversion / 12 inner conversion operand / 13 leaf (EInt 5).
   Each stored metadatum is derived from the UNIVERSAL exactness theorem (rewrite by build_file_source_exact,
   then compute the INDEPENDENT source spec) — NEVER by unfolding the builder.  A wrong builder kind / role /
   parent / index / subtree makes [build_file_source_exact] unprovable, so these pin exact per-occurrence
   labels; the repeated EInt 1 args (ids 5,6) are NOT collapsed, and the nested conversion chain (11->12->13)
   pins the RConversionOperand relationship. ---------- *)
Definition wf : GoSourceFile := main_source
  [ DMain [ SPrintln [ EInt 1%N ; EInt 1%N ] ; SPrintln [ EBool true ] ]
  ; DMain [ SPrintln [ EIntConvert IInt (EIntConvert IInt8 (EInt 5%N)) ] ] ].

Ltac wf_meta := rewrite build_file_source_exact; vm_compute; reflexivity.
Example wf_meta_file  : NodeTable.get 1%positive  (fi_table (build_file wf)) = Some (mkMeta KFile         None      RFileRoot        13). Proof. wf_meta. Qed.
Example wf_meta_pkg   : NodeTable.get 2%positive  (fi_table (build_file wf)) = Some (mkMeta KPackageClause (Some 1)  RFilePackage      2). Proof. wf_meta. Qed.
Example wf_meta_decl0 : NodeTable.get 3%positive  (fi_table (build_file wf)) = Some (mkMeta KTopLevelDecl  (Some 1)  (RFileDecl 0)     8). Proof. wf_meta. Qed.
Example wf_meta_stmt0 : NodeTable.get 4%positive  (fi_table (build_file wf)) = Some (mkMeta KStatement     (Some 3)  (RDeclStmt 0)     6). Proof. wf_meta. Qed.
Example wf_meta_arg0  : NodeTable.get 5%positive  (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 4)  (RPrintlnArg 0)   5). Proof. wf_meta. Qed.
Example wf_meta_arg1  : NodeTable.get 6%positive  (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 4)  (RPrintlnArg 1)   6). Proof. wf_meta. Qed.
Example wf_meta_stmt1 : NodeTable.get 7%positive  (fi_table (build_file wf)) = Some (mkMeta KStatement     (Some 3)  (RDeclStmt 1)     8). Proof. wf_meta. Qed.
Example wf_meta_bool  : NodeTable.get 8%positive  (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 7)  (RPrintlnArg 0)   8). Proof. wf_meta. Qed.
Example wf_meta_decl1 : NodeTable.get 9%positive  (fi_table (build_file wf)) = Some (mkMeta KTopLevelDecl  (Some 1)  (RFileDecl 1)    13). Proof. wf_meta. Qed.
Example wf_meta_stmt2 : NodeTable.get 10%positive (fi_table (build_file wf)) = Some (mkMeta KStatement     (Some 9)  (RDeclStmt 0)    13). Proof. wf_meta. Qed.
Example wf_meta_conv0 : NodeTable.get 11%positive (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 10) (RPrintlnArg 0)  13). Proof. wf_meta. Qed.
Example wf_meta_conv1 : NodeTable.get 12%positive (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 11) RConversionOperand 13). Proof. wf_meta. Qed.
Example wf_meta_leaf  : NodeTable.get 13%positive (fi_table (build_file wf)) = Some (mkMeta KExpression    (Some 12) RConversionOperand 13). Proof. wf_meta. Qed.
Example wf_meta_absent : NodeTable.get 14%positive (fi_table (build_file wf)) = None. Proof. wf_meta. Qed.

(* source-VIEW recovery: the INDEPENDENT spec recovers the exact original fragment (the [occurrence_view] that
   [occurrence_meta] erases) for each occurrence kind — package clause / an argument / the innermost leaf. *)
Example wf_view_pkg  : source_occurrence_at wf 2%positive
  = Some (mkOcc KPackageClause (ViewPackageClause PkgMain) (Some 1%positive) RFilePackage 2%positive).
Proof. vm_compute. reflexivity. Qed.
Example wf_view_arg0 : source_occurrence_at wf 5%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 1%N)) (Some 4%positive) (RPrintlnArg 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Example wf_view_leaf : source_occurrence_at wf 13%positive
  = Some (mkOcc KExpression (ViewExpression (EInt 5%N)) (Some 12%positive) RConversionOperand 13%positive).
Proof. vm_compute. reflexivity. Qed.
