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

From Stdlib Require Import PArith List Bool Lia.
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
