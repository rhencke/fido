(** * Index — the production occurrence index over the ONE raw [Syntax.Program] (Source Forest campaign).

    [Index] derives, from one exact immutable [Syntax.Program] snapshot, a canonical file-local occurrence
    identity for every currently-represented semantic source occurrence, a certified structural index over
    the ORIGINAL source forest, snapshot-indexed validated references, total navigation, and an indexed
    traversal that supplies the original syntax fragment and its canonical reference together.  It is
    STRUCTURAL and SOURCE-derived: it imports only [Syntax] (the one source AST), [Collections] (the standard
    map foundation), and [FilePath.T]; it does NOT know semantic types, compiler acceptance, rendering, or
    diagnostics (it must not import [Typing]/[Admissible]/[Property]/[Render]/[Emit]).

    COLLECTION LAW (CLAUDE.md rule 10 / ARCHITECTURE.md): the per-file local-node table is the STANDARD
    pinned-stdlib positive-key map [FMapPositive.PositiveMap] (aliased [Collections.NodeMap]); the outer
    program index is the STANDARD [FMapAVL] file map ([Collections.FileMap]) keyed by [FilePath.T].  Fido
    authors NO collection storage or generic collection algorithm; the thin sealed [Table] wrapper stores
    a [Collections.NodeMap] and proves its three laws directly from the standard map facts.  RETAINS
    these selected standard maps (the sealing hides the map CONSTRUCTORS and RAW operations, NOT the choice of
    collection).

    The indexed traversal ([visit_file] running the single-pass [walk_file]) pairs each ORIGINAL syntax
    fragment with its validated [NodeRef] in one pass — CONSUMED by [Admissible]'s production elaboration
    ([elaborate]) as the ONE indexed whole-program pass. *)

From Stdlib Require Import PArith NArith List Bool Lia Sorted Recdef Wf_nat Arith Eqdep_dec String.
From Stdlib Require Import Structures.OrderedType FSets.FMapAVL FSets.FMapFacts SetoidList.
(* The binding import boundary: Index imports ONLY [Syntax] / [Collections] / [FilePath.T] +
   axiom-free stdlib.  The raw-syntax payload types ([Integer.Kind] / [Float.Decimal] / … / the
   [ModulePath.T] / [Version] used only in the regression fixtures) are reached by QUALIFIED name through the
   modules [Syntax] already loads — NEVER a direct import of a semantic module. *)
From Fido Require Import FilePath Collections Syntax.
Import ListNotations.
Local Open Scope positive_scope.

(** ** The SELECTED node table: an ABSTRACT interface, implemented internally by the STANDARD pinned-stdlib *)
(* positive-key map [Collections.NodeMap] ([FMapPositive]).  Callers see ONLY                       *)
(* [Table.table]/[empty]/[get]/[set] and the three laws; the sealing hides the standard map's        *)
(* CONSTRUCTORS and RAW operations, NOT the choice of collection. *)

Module Type TABLE.
  Parameter table : Type -> Type.
  Parameter empty : forall {A}, table A.
  Parameter get   : forall {A}, positive -> table A -> option A.
  Parameter set   : forall {A}, positive -> A -> table A -> table A.
  Parameter get_empty     : forall {A} (k : positive), get k (@empty A) = None.
  Parameter get_set_same  : forall {A} (k : positive) (v : A) (t : table A), get k (set k v t) = Some v.
  Parameter get_set_other : forall {A} (j k : positive) (v : A) (t : table A),
    j <> k -> get k (set j v t) = get k t.
End TABLE.

Module Table : TABLE.
  Definition table := Collections.NodeMap.t.
  Definition empty {A} : table A := Collections.NodeMap.empty A.
  Definition get {A} (k : positive) (t : table A) : option A := Collections.NodeMap.find k t.
  Definition set {A} (k : positive) (v : A) (t : table A) : table A := Collections.NodeMap.add k v t.
  Lemma get_empty {A} (k : positive) : get k (@empty A) = None.
  Proof. apply Collections.NodeMap.gempty. Qed.
  Lemma get_set_same {A} (k : positive) (v : A) (t : table A) : get k (set k v t) = Some v.
  Proof. apply Collections.NodeMap.gss. Qed.
  Lemma get_set_other {A} (j k : positive) (v : A) (t : table A) :
    j <> k -> get k (set j v t) = get k t.
  Proof. intro H. apply Collections.NodeMap.gso. congruence. Qed.
End Table.

(** ** Occurrence kinds, roles, and metadata.                                       *)

(* The current occurrence universe: file root, package clause, top-level declaration, statement, expression,
   and the source TYPE NAME of an explicit conversion target.  No kind for unsupported future syntax (no
   import kind, no arbitrary/qualified type-syntax kind ahead of its syntax). *)
Inductive Kind := FileKind | PackageClauseKind | DeclarationKind | StatementKind | ExpressionKind | TypeNameKind.

(* How an occurrence participates in its parent.  An explicit conversion has TWO children in source order:
   its source type-name TARGET, then its OPERAND expression. *)
Inductive Role :=
| FileRoot                  (* the file root itself *)
| FilePackage               (* the file's package clause *)
| FileDeclaration (n : nat)        (* the n-th top-level declaration of a file *)
| DeclarationStatement (n : nat)        (* the n-th statement in a declaration body *)
| PrintlnArgument (n : nat)      (* the n-th argument of a println statement *)
| ConversionTarget          (* the source type-name target of an explicit conversion expression *)
| ConversionOperand.        (* the single operand of an explicit conversion expression *)

(* Small structural metadata; NO copy of the recursive subtree. *)
Record Meta := MakeMeta {
  kind        : Kind;
  parent      : option positive;   (* file-local parent id; None only for a file root *)
  role        : Role;
  subtree_end : positive           (* last preorder id in this occurrence's subtree *)
}.

Definition root_id : positive := 1.       (* every file root's canonical local id *)
Definition package_id  : positive := 2.       (* the package clause is the file root's first child = Pos.succ root_id *)

(* total extraction from a provably-present option — the basis for the total validated-reference API. *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* [Syntax.ImportSpec] is EMPTY, so any [list Syntax.ImportSpec] is intrinsically [nil]; the builder and the
   source spec STRUCTURALLY consume [Syntax.imports] so a future import constructor forces
   this definition and its proofs to change rather than being silently ignored. *)
Lemma import_list_nil : forall (l : list Syntax.ImportSpec), l = [].
Proof. intros [|i rest]; [ reflexivity | destruct i ]. Qed.

(** ** The one-pass per-file index builder.                                             *)
(* Each builder threads a fresh-id counter and inserts each occurrence's metadata EXACTLY ONCE via  *)
(* one standard-map [Table.set]; it never searches, compares, or copies syntax subtrees.  A      *)
(* subtree builder returns the subtree's last id ([se], its [subtree_end]); a sibling-sequence       *)
(* builder returns the next free id.  Meta for an internal node is inserted AFTER its children so     *)
(* [subtree_end] is known.  Expression leaves have no child; an explicit conversion has exactly one   *)
(* operand child (role [ConversionOperand]). *)

Fixpoint build_expr (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr)
                    (t : Table.table Meta) : Table.table Meta * positive (* subtree_end *) :=
  match e with
  | Syntax.BoolLiteral _ | Syntax.IntegerLiteral _ | Syntax.NegatedIntegerLiteral _ | Syntax.StringLiteral _ | Syntax.FloatLiteral _ | Syntax.ComplexLiteral _ =>
      (Table.set me (MakeMeta ExpressionKind (Some parent) role me) t, me)
  | Syntax.Convert _ x =>
      (* two children in source order: the type-name TARGET (a leaf at [me+1]), then the OPERAND subtree. *)
      let tn := Pos.succ me in
      let t_tn := Table.set tn (MakeMeta TypeNameKind (Some me) ConversionTarget tn) t in
      let '(t1, e1) := build_expr me ConversionOperand (Pos.succ tn) x t_tn in
      (Table.set me (MakeMeta ExpressionKind (Some parent) role e1) t1, e1)
  end.

(* one println argument: an expression subtree carrying its argument role. *)
Definition build_arg (parent : positive) (aidx : nat) (me : positive) (e : Syntax.Expr)
                     (t : Table.table Meta) : Table.table Meta * positive :=
  build_expr parent (PrintlnArgument aidx) me e t.

(* A generic left-to-right sibling-sequence builder: builds each element as a subtree rooted at the running
   fresh id and advances.  Returns the next free id.  [bx] is the per-element subtree builder. *)
Fixpoint build_seq {X} (bx : positive -> nat -> positive -> X -> Table.table Meta -> Table.table Meta * positive)
                   (parent : positive) (i0 : nat) (me0 : positive) (xs : list X) (t : Table.table Meta)
  : Table.table Meta * positive (* next free id *) :=
  match xs with
  | []        => (t, me0)
  | x :: rest =>
      let '(t1, se) := bx parent i0 me0 x t in
      build_seq bx parent (S i0) (Pos.succ se) rest t1
  end.

(* a statement wraps a left-to-right run of println-argument subtrees. *)
Definition build_stmt (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt)
                      (t : Table.table Meta) : Table.table Meta * positive :=
  match s with
  | Syntax.Println args =>
      let '(t1, nx) := build_seq build_arg me 0 (Pos.succ me) args t in
      (Table.set me (MakeMeta StatementKind (Some parent) (DeclarationStatement sidx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

(* a declaration wraps a left-to-right run of statement subtrees. *)
Definition build_decl (parent : positive) (didx : nat) (me : positive) (d : Syntax.Decl)
                      (t : Table.table Meta) : Table.table Meta * positive :=
  match d with
  | Syntax.Main body =>
      let '(t1, nx) := build_seq build_stmt me 0 (Pos.succ me) body t in
      (Table.set me (MakeMeta DeclarationKind (Some parent) (FileDeclaration didx) (Pos.pred nx)) t1, Pos.pred nx)
  end.

(* The per-file index carries NO path (the path is the outer map key — no second file identity). *)
Record File := MakeFile {
  table : Table.table Meta;
  count : positive           (* number of occurrences = last local id; ids are [1 .. count] *)
}.

(* The file root's children in canonical preorder are the package clause (id [package_id] = 2) then the
   declarations (from id 3).  [Syntax.imports] is STRUCTURALLY consumed: it is intrinsically
   [nil] today, so no import occurrence exists; a future import constructor makes the [i :: _] branch
   constructible and forces this definition and its proofs to change. *)
Definition build_file (f : Syntax.File) : File :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      let tp := Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty in
      let '(t1, nx) := build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) tp in
      let cnt := Pos.pred nx in
      MakeFile (Table.set root_id (MakeMeta FileKind None FileRoot cnt) t1) cnt
  end.

(** ** Boundary functions: the last preorder id of a subtree / the next free id after a sibling run.   *)
(* These are TABLE-FREE — derived purely from source structure — and shared by the builder-agnostic  *)
(* source-occurrence specification below.                                                            *)

Fixpoint end_expr (me : positive) (e : Syntax.Expr) : positive :=
  match e with
  | Syntax.BoolLiteral _ | Syntax.IntegerLiteral _ | Syntax.NegatedIntegerLiteral _ | Syntax.StringLiteral _ | Syntax.FloatLiteral _ | Syntax.ComplexLiteral _ => me
  | Syntax.Convert _ x => end_expr (Pos.succ (Pos.succ me)) x   (* [me]=conv, [me+1]=type name, operand from [me+2] *)
  end.
Fixpoint next_exprs (me : positive) (es : list Syntax.Expr) : positive :=
  match es with [] => me | e :: rest => next_exprs (Pos.succ (end_expr me e)) rest end.
Definition end_stmt (me : positive) (s : Syntax.Stmt) : positive :=
  match s with Syntax.Println args => Pos.pred (next_exprs (Pos.succ me) args) end.
Fixpoint next_stmts (me : positive) (ss : list Syntax.Stmt) : positive :=
  match ss with [] => me | s :: rest => next_stmts (Pos.succ (end_stmt me s)) rest end.
Definition end_decl (me : positive) (d : Syntax.Decl) : positive :=
  match d with Syntax.Main body => Pos.pred (next_stmts (Pos.succ me) body) end.
Fixpoint next_decls (me : positive) (ds : list Syntax.Decl) : positive :=
  match ds with [] => me | d :: rest => next_decls (Pos.succ (end_decl me d)) rest end.
Definition count_file (f : Syntax.File) : positive := Pos.pred (next_decls (Pos.succ package_id) (Syntax.declarations f)).

(* --- the builder's returned subtree-end / next-free-id agree with the table-free boundary functions. --- *)

Lemma build_expr_end : forall e parent role me t, snd (build_expr parent role me e t) = end_expr me e.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me t; try reflexivity.
  cbn [build_expr end_expr].
  specialize (IHx me ConversionOperand (Pos.succ (Pos.succ me))
    (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t)).
  destruct (build_expr me ConversionOperand (Pos.succ (Pos.succ me)) x
    (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t)) as [t1 e1].
  cbn [snd] in IHx |- *. exact IHx.
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

Lemma build_file_count : forall f, count (build_file f) = count_file f.
Proof.
  intros f. unfold build_file, count_file. destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  rewrite <- (build_seq_decl_next (Syntax.declarations f) root_id 0 (Pos.succ package_id)
                (Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty)).
  destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f)
              (Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty))
    as [t1 nx].
  reflexivity.
Qed.

(** ** An INDEPENDENT source-occurrence specification (table-free, builder-independent).          *)
(* For a source file and a local preorder id, this states — purely from the source syntax and the    *)
(* boundary functions above — the EXACT occurrence that id designates and the metadata it SHOULD      *)
(* carry.  It never consults [Table], [build_*], or [File]; it is the semantic yardstick      *)
(* against which [build_file] is proved correct in [build_file_source_exact].                         *)

(* a kind-indexed view onto the ORIGINAL syntax fragment (no copied/parallel grammar). *)
Inductive View : Kind -> Type :=
| FileView          : Syntax.File -> View FileKind
| PackageClauseView : Syntax.PackageClause -> View PackageClauseKind
| DeclarationView  : Syntax.Decl -> View DeclarationKind
| StatementView     : Syntax.Stmt -> View StatementKind
| ExpressionView    : Syntax.Expr -> View ExpressionKind
| TypeNameView      : Syntax.TypeExpr -> View TypeNameKind.

Record Occurrence := MakeOccurrence {
  occurrence_kind        : Kind;
  occurrence_view        : View occurrence_kind;
  occurrence_parent      : option positive;
  occurrence_role        : Role;
  occurrence_subtree_end : positive
}.

(* the metadata an occurrence SHOULD carry — derived only from the occurrence, NEVER from the builder. *)
Definition occurrence_meta (o : Occurrence) : Meta :=
  MakeMeta (occurrence_kind o) (occurrence_parent o) (occurrence_role o) (occurrence_subtree_end o).

(* the original expression fragment an occurrence's view carries (Some only for expression occurrences). *)
Definition view_expr (o : Occurrence) : option Syntax.Expr :=
  match occurrence_view o with ExpressionView e => Some e | _ => None end.

(* [view_expr] is [Some] EXACTLY for a [ExpressionKind] occurrence (the dependent [View] forces the kind). *)
Lemma view_expr_kind : forall o e, view_expr o = Some e -> occurrence_kind o = ExpressionKind.
Proof.
  intros [k v par role sub] e H. cbn [view_expr occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.
Lemma kind_view_expr : forall o, occurrence_kind o = ExpressionKind -> exists e, view_expr o = Some e.
Proof.
  intros [k v par role sub] H. cbn [occurrence_kind] in H. subst k.
  cbn [view_expr occurrence_view].
  refine (match v as v0 in View k0
          return (match k0 return Prop with
                  | ExpressionKind => exists ex, (match v0 with ExpressionView e => Some e | _ => None end) = Some ex
                  | _ => True end)
          with
          | ExpressionView e => ex_intro _ e eq_refl
          | FileView _ => I | PackageClauseView _ => I | DeclarationView _ => I | StatementView _ => I
          | TypeNameView _ => I
          end).
Qed.

(* the original type-name syntax an occurrence's view carries (Some only for type-name occurrences). *)
Definition view_typename (o : Occurrence) : option Syntax.TypeExpr :=
  match occurrence_view o with TypeNameView ts => Some ts | _ => None end.
Lemma view_typename_kind : forall o ts, view_typename o = Some ts -> occurrence_kind o = TypeNameKind.
Proof.
  intros [k v par role sub] ts H. cbn [view_typename occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.
Lemma kind_view_typename : forall o, occurrence_kind o = TypeNameKind -> exists ts, view_typename o = Some ts.
Proof.
  intros [k v par role sub] H. cbn [occurrence_kind] in H. subst k.
  cbn [view_typename occurrence_view].
  refine (match v as v0 in View k0
          return (match k0 return Prop with
                  | TypeNameKind => exists tx, (match v0 with TypeNameView ts => Some ts | _ => None end) = Some tx
                  | _ => True end)
          with
          | TypeNameView ts => ex_intro _ ts eq_refl
          | FileView _ => I | PackageClauseView _ => I | DeclarationView _ => I | StatementView _ => I
          | ExpressionView _ => I
          end).
Qed.

(* the occurrence a preorder id designates inside one expression subtree rooted at [me]. *)
Fixpoint occurrence_expr' (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr) (target : positive)
  : option Occurrence :=
  match e with
  | Syntax.BoolLiteral _ | Syntax.IntegerLiteral _ | Syntax.NegatedIntegerLiteral _ | Syntax.StringLiteral _ | Syntax.FloatLiteral _ | Syntax.ComplexLiteral _ =>
      if Pos.eqb target me then Some (MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role me) else None
  | Syntax.Convert ts x =>
      if Pos.eqb target me
      then Some (MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (end_expr me e))
      else if Pos.eqb target (Pos.succ me)
      then Some (MakeOccurrence TypeNameKind (TypeNameView ts) (Some me) ConversionTarget (Pos.succ me))
      else occurrence_expr' me ConversionOperand (Pos.succ (Pos.succ me)) x target
  end.
Fixpoint occurrence_exprs' (parent : positive) (aidx : nat) (me : positive) (es : list Syntax.Expr) (target : positive)
  : option Occurrence :=
  match es with
  | [] => None
  | e :: rest =>
      if Pos.leb target (end_expr me e)
      then occurrence_expr' parent (PrintlnArgument aidx) me e target
      else occurrence_exprs' parent (S aidx) (Pos.succ (end_expr me e)) rest target
  end.
Definition occurrence_stmt' (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt) (target : positive)
  : option Occurrence :=
  match s with
  | Syntax.Println args =>
      if Pos.eqb target me
      then Some (MakeOccurrence StatementKind (StatementView s) (Some parent) (DeclarationStatement sidx) (end_stmt me s))
      else occurrence_exprs' me 0 (Pos.succ me) args target
  end.
Fixpoint occurrence_stmts' (parent : positive) (sidx : nat) (me : positive) (ss : list Syntax.Stmt) (target : positive)
  : option Occurrence :=
  match ss with
  | [] => None
  | s :: rest =>
      if Pos.leb target (end_stmt me s)
      then occurrence_stmt' parent sidx me s target
      else occurrence_stmts' parent (S sidx) (Pos.succ (end_stmt me s)) rest target
  end.
Definition occurrence_decl' (parent : positive) (didx : nat) (me : positive) (d : Syntax.Decl) (target : positive)
  : option Occurrence :=
  match d with
  | Syntax.Main body =>
      if Pos.eqb target me
      then Some (MakeOccurrence DeclarationKind (DeclarationView d) (Some parent) (FileDeclaration didx) (end_decl me d))
      else occurrence_stmts' me 0 (Pos.succ me) body target
  end.
Fixpoint occurrence_decls' (parent : positive) (didx : nat) (me : positive) (ds : list Syntax.Decl) (target : positive)
  : option Occurrence :=
  match ds with
  | [] => None
  | d :: rest =>
      if Pos.leb target (end_decl me d)
      then occurrence_decl' parent didx me d target
      else occurrence_decls' parent (S didx) (Pos.succ (end_decl me d)) rest target
  end.
Definition source_occurrence_at (f : Syntax.File) (target : positive) : option Occurrence :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      if Pos.eqb target root_id
      then Some (MakeOccurrence FileKind (FileView f) None FileRoot (count_file f))
      else if Pos.eqb target package_id
           then Some (MakeOccurrence PackageClauseKind (PackageClauseView (Syntax.package f)) (Some root_id) FilePackage package_id)
           else occurrence_decls' root_id 0 (Pos.succ package_id) (Syntax.declarations f) target
  end.

(* --- interval frame lemmas: an occurrence lookup outside a subtree's [me .. end] window is [None]. --- *)

Lemma end_expr_ge : forall e me, (me <= end_expr me e)%positive.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros me; try (cbn [end_expr]; lia);
    (cbn [end_expr]; specialize (IHx (Pos.succ (Pos.succ me))); lia).
Qed.

Lemma occurrence_expr'_below : forall e parent role me target,
  (target < me)%positive -> occurrence_expr' parent role me e target = None.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me target Hlt; cbn [occurrence_expr'];
    try (destruct (Pos.eqb_spec target me); [lia|reflexivity]);
    (destruct (Pos.eqb_spec target me); [lia|];
     destruct (Pos.eqb_spec target (Pos.succ me)); [lia|]; apply IHx; lia).
Qed.

Lemma occurrence_expr'_above : forall e parent role me target,
  (end_expr me e < target)%positive -> occurrence_expr' parent role me e target = None.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me target Hgt; cbn [occurrence_expr' end_expr] in *;
    try (destruct (Pos.eqb_spec target me); [lia|reflexivity]);
    (pose proof (end_expr_ge x (Pos.succ (Pos.succ me))) as Hx;
     destruct (Pos.eqb_spec target me); [lia|];
     destruct (Pos.eqb_spec target (Pos.succ me)); [lia|]; apply IHx; exact Hgt).
Qed.

Lemma next_exprs_ge : forall es me, (me <= next_exprs me es)%positive.
Proof.
  induction es as [|e rest IH]; intros me; cbn [next_exprs]; [lia|].
  specialize (IH (Pos.succ (end_expr me e))). pose proof (end_expr_ge e me) as He. lia.
Qed.

Lemma occurrence_exprs'_below : forall es parent aidx me target,
  (target < me)%positive -> occurrence_exprs' parent aidx me es target = None.
Proof.
  induction es as [|e rest IH]; intros parent aidx me target Hlt; cbn [occurrence_exprs']; [reflexivity|].
  pose proof (end_expr_ge e me) as He.
  destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
  - apply occurrence_expr'_below. exact Hlt.
  - lia.
Qed.

Lemma occurrence_exprs'_above : forall es parent aidx me target,
  (next_exprs me es <= target)%positive -> occurrence_exprs' parent aidx me es target = None.
Proof.
  induction es as [|e rest IH]; intros parent aidx me target Hge; cbn [occurrence_exprs' next_exprs] in *; [reflexivity|].
  pose proof (next_exprs_ge rest (Pos.succ (end_expr me e))) as Hn.
  destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
  - lia.
  - apply IH. lia.
Qed.

Lemma end_stmt_ge : forall s me, (me <= end_stmt me s)%positive.
Proof.
  intros [args] me. cbn [end_stmt]. pose proof (next_exprs_ge args (Pos.succ me)) as Hn. lia.
Qed.

Lemma occurrence_stmt'_below : forall s parent sidx me target,
  (target < me)%positive -> occurrence_stmt' parent sidx me s target = None.
Proof.
  intros [args] parent sidx me target Hlt. cbn [occurrence_stmt'].
  destruct (Pos.eqb_spec target me); [lia|]. apply occurrence_exprs'_below. lia.
Qed.

Lemma occurrence_stmt'_above : forall s parent sidx me target,
  (end_stmt me s < target)%positive -> occurrence_stmt' parent sidx me s target = None.
Proof.
  intros [args] parent sidx me target Hgt. cbn [occurrence_stmt' end_stmt] in *.
  pose proof (next_exprs_ge args (Pos.succ me)) as Hn.
  destruct (Pos.eqb_spec target me); [lia|]. apply occurrence_exprs'_above. lia.
Qed.

Lemma next_stmts_ge : forall ss me, (me <= next_stmts me ss)%positive.
Proof.
  induction ss as [|s rest IH]; intros me; cbn [next_stmts]; [lia|].
  specialize (IH (Pos.succ (end_stmt me s))). pose proof (end_stmt_ge s me) as Hs. lia.
Qed.

Lemma occurrence_stmts'_below : forall ss parent sidx me target,
  (target < me)%positive -> occurrence_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hlt; cbn [occurrence_stmts']; [reflexivity|].
  pose proof (end_stmt_ge s me) as Hs.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - apply occurrence_stmt'_below. exact Hlt.
  - lia.
Qed.

Lemma occurrence_stmts'_above : forall ss parent sidx me target,
  (next_stmts me ss <= target)%positive -> occurrence_stmts' parent sidx me ss target = None.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me target Hge; cbn [occurrence_stmts' next_stmts] in *; [reflexivity|].
  pose proof (next_stmts_ge rest (Pos.succ (end_stmt me s))) as Hn.
  destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
  - lia.
  - apply IH. lia.
Qed.

Lemma end_decl_ge : forall d me, (me <= end_decl me d)%positive.
Proof.
  intros [body] me. cbn [end_decl]. pose proof (next_stmts_ge body (Pos.succ me)) as Hn. lia.
Qed.

Lemma occurrence_decl'_below : forall d parent didx me target,
  (target < me)%positive -> occurrence_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hlt. cbn [occurrence_decl'].
  destruct (Pos.eqb_spec target me); [lia|]. apply occurrence_stmts'_below. lia.
Qed.

Lemma occurrence_decl'_above : forall d parent didx me target,
  (end_decl me d < target)%positive -> occurrence_decl' parent didx me d target = None.
Proof.
  intros [body] parent didx me target Hgt. cbn [occurrence_decl' end_decl] in *.
  pose proof (next_stmts_ge body (Pos.succ me)) as Hn.
  destruct (Pos.eqb_spec target me); [lia|]. apply occurrence_stmts'_above. lia.
Qed.

Lemma occurrence_decls'_below : forall ds parent didx me target,
  (target < me)%positive -> occurrence_decls' parent didx me ds target = None.
Proof.
  induction ds as [|d rest IH]; intros parent didx me target Hlt; cbn [occurrence_decls']; [reflexivity|].
  pose proof (end_decl_ge d me) as Hd.
  destruct (Pos.leb_spec target (end_decl me d)) as [Hle|Hgt].
  - apply occurrence_decl'_below. exact Hlt.
  - lia.
Qed.

(* --- the builder AGREES with the independent spec: the table built for a subtree holds exactly the
       source occurrence's metadata at every id in its window, and leaves every id outside untouched. --- *)

Lemma build_expr_get : forall e parent role me t target,
  Table.get target (fst (build_expr parent role me e t)) =
    match occurrence_expr' parent role me e target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me t target; cbn [build_expr occurrence_expr'];
    (* leaves *)
    try (cbn [fst]; destruct (Pos.eqb_spec target me);
         [ subst; rewrite Table.get_set_same; reflexivity
         | rewrite Table.get_set_other by congruence; reflexivity ]).
  (* conversion: a type-name child at [me+1], then the operand subtree from [me+2] *)
  set (t_tn := Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t).
  pose proof (build_expr_end x me ConversionOperand (Pos.succ (Pos.succ me)) t_tn) as He1.
  destruct (build_expr me ConversionOperand (Pos.succ (Pos.succ me)) x t_tn) as [t1 e1] eqn:E1.
  cbn [snd] in He1; subst e1; cbn [fst].
  specialize (IHx me ConversionOperand (Pos.succ (Pos.succ me)) t_tn target).
  rewrite E1 in IHx; cbn [fst] in IHx.
  destruct (Pos.eqb_spec target me) as [->|Hne_me].
  { rewrite Table.get_set_same; reflexivity. }
  rewrite Table.get_set_other by congruence.
  destruct (Pos.eqb_spec target (Pos.succ me)) as [->|Hne_tn].
  { rewrite IHx.
    rewrite (occurrence_expr'_below x me ConversionOperand (Pos.succ (Pos.succ me)) (Pos.succ me)) by lia.
    subst t_tn; rewrite Table.get_set_same; reflexivity. }
  rewrite IHx.
  destruct (occurrence_expr' me ConversionOperand (Pos.succ (Pos.succ me)) x target) as [o|] eqn:Eo.
  - reflexivity.
  - subst t_tn; rewrite Table.get_set_other by congruence; reflexivity.
Qed.

Lemma build_arg_get : forall e parent aidx me t target,
  Table.get target (fst (build_arg parent aidx me e t)) =
    match occurrence_expr' parent (PrintlnArgument aidx) me e target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof. intros. apply build_expr_get. Qed.

Lemma build_seq_arg_get : forall args parent aidx me t target,
  Table.get target (fst (build_seq build_arg parent aidx me args t)) =
    match occurrence_exprs' parent aidx me args target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  induction args as [|e rest IH]; intros parent aidx me t target; cbn [build_seq occurrence_exprs'].
  - reflexivity.
  - pose proof (build_arg_end e parent aidx me t) as He.
    destruct (build_arg parent aidx me e t) as [t1 se] eqn:E1. cbn [snd] in He. subst se. cbn [fst].
    specialize (IH parent (S aidx) (Pos.succ (end_expr me e)) t1 target). rewrite IH.
    specialize (build_arg_get e parent aidx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_expr me e)) as [Hle|Hgt].
    + rewrite (occurrence_exprs'_below rest parent (S aidx) (Pos.succ (end_expr me e)) target ltac:(lia)). reflexivity.
    + rewrite (occurrence_expr'_above e parent (PrintlnArgument aidx) me target ltac:(lia)). reflexivity.
Qed.

Lemma build_stmt_get : forall s parent sidx me t target,
  Table.get target (fst (build_stmt parent sidx me s t)) =
    match occurrence_stmt' parent sidx me s target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  intros [args] parent sidx me t target. cbn [build_stmt occurrence_stmt'].
  pose proof (build_seq_arg_next args me 0 (Pos.succ me) t) as Hnx.
  destruct (build_seq build_arg me 0 (Pos.succ me) args t) as [t1 nx] eqn:E1. cbn [snd] in Hnx. subst nx.
  cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite Table.get_set_same. reflexivity.
  - rewrite Table.get_set_other by congruence.
    specialize (build_seq_arg_get args me 0 (Pos.succ me) t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. exact HG.
Qed.

Lemma build_seq_stmt_get : forall ss parent sidx me t target,
  Table.get target (fst (build_seq build_stmt parent sidx me ss t)) =
    match occurrence_stmts' parent sidx me ss target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me t target; cbn [build_seq occurrence_stmts'].
  - reflexivity.
  - pose proof (build_stmt_end s parent sidx me t) as Hse.
    destruct (build_stmt parent sidx me s t) as [t1 se] eqn:E1. cbn [snd] in Hse. subst se. cbn [fst].
    specialize (IH parent (S sidx) (Pos.succ (end_stmt me s)) t1 target). rewrite IH.
    specialize (build_stmt_get s parent sidx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_stmt me s)) as [Hle|Hgt].
    + rewrite (occurrence_stmts'_below rest parent (S sidx) (Pos.succ (end_stmt me s)) target ltac:(lia)). reflexivity.
    + rewrite (occurrence_stmt'_above s parent sidx me target ltac:(lia)). reflexivity.
Qed.

Lemma build_decl_get : forall d parent didx me t target,
  Table.get target (fst (build_decl parent didx me d t)) =
    match occurrence_decl' parent didx me d target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  intros [body] parent didx me t target. cbn [build_decl occurrence_decl'].
  pose proof (build_seq_stmt_next body me 0 (Pos.succ me) t) as Hnx.
  destruct (build_seq build_stmt me 0 (Pos.succ me) body t) as [t1 nx] eqn:E1. cbn [snd] in Hnx. subst nx.
  cbn [fst].
  destruct (Pos.eqb_spec target me).
  - subst. rewrite Table.get_set_same. reflexivity.
  - rewrite Table.get_set_other by congruence.
    specialize (build_seq_stmt_get body me 0 (Pos.succ me) t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. exact HG.
Qed.

Lemma build_seq_decl_get : forall ds parent didx me t target,
  Table.get target (fst (build_seq build_decl parent didx me ds t)) =
    match occurrence_decls' parent didx me ds target with
    | Some o => Some (occurrence_meta o)
    | None   => Table.get target t
    end.
Proof.
  induction ds as [|d rest IH]; intros parent didx me t target; cbn [build_seq occurrence_decls'].
  - reflexivity.
  - pose proof (build_decl_end d parent didx me t) as Hde.
    destruct (build_decl parent didx me d t) as [t1 de] eqn:E1. cbn [snd] in Hde. subst de. cbn [fst].
    specialize (IH parent (S didx) (Pos.succ (end_decl me d)) t1 target). rewrite IH.
    specialize (build_decl_get d parent didx me t target) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.leb_spec target (end_decl me d)) as [Hle|Hgt].
    + rewrite (occurrence_decls'_below rest parent (S didx) (Pos.succ (end_decl me d)) target ltac:(lia)). reflexivity.
    + rewrite (occurrence_decl'_above d parent didx me target ltac:(lia)). reflexivity.
Qed.

(* ============ the load-bearing UNIVERSAL exactness theorem. ============ *)

(* the metadata the builder stores at EVERY local id is EXACTLY the metadata of the source occurrence that
   id designates — both presence (a real occurrence -> its meta) and absence (no occurrence -> no entry).
   It ranges over every positive id, needs no pre-existing reference, and never assumes the id is valid.
   A structurally-coherent MISLABELING (package clause as a declaration, leaf as a statement, shifted index,
   wrong parent/subtree, deduplicated repeated argument) makes the two sides disagree, so it CANNOT satisfy
   this equality. *)
Theorem build_file_source_exact : forall f local,
  Table.get local (table (build_file f)) = option_map occurrence_meta (source_occurrence_at f local).
Proof.
  intros f local. unfold build_file, source_occurrence_at.
  destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  set (tp := Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty).
  pose proof (build_seq_decl_next (Syntax.declarations f) root_id 0 (Pos.succ package_id) tp) as Hnx.
  destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) tp) as [t1 nx] eqn:E1.
  cbn [snd] in Hnx. subst nx. cbn [table].
  destruct (Pos.eqb_spec local root_id).
  - (* file root *)
    subst. rewrite Table.get_set_same.
    cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
    unfold count_file. reflexivity.
  - rewrite Table.get_set_other by congruence.
    specialize (build_seq_decl_get (Syntax.declarations f) root_id 0 (Pos.succ package_id) tp local) as HG.
    rewrite E1 in HG. cbn [fst] in HG. rewrite HG.
    destruct (Pos.eqb_spec local package_id).
    + (* package clause: below the decl window, so the decl spec is None; read it out of [tp] *)
      subst local.
      rewrite (occurrence_decls'_below (Syntax.declarations f) root_id 0 (Pos.succ package_id) package_id
                 ltac:(unfold package_id; lia)).
      unfold tp. rewrite Table.get_set_same.
      cbn [option_map occurrence_meta occurrence_kind occurrence_parent occurrence_role occurrence_subtree_end].
      reflexivity.
    + (* declaration region: [tp] holds nothing here (local <> package_id), so both sides agree via the decl spec *)
      unfold tp. rewrite Table.get_set_other by congruence. rewrite Table.get_empty.
      destruct (occurrence_decls' root_id 0 (Pos.succ package_id) (Syntax.declarations f) local) as [o|];
        cbn [option_map]; reflexivity.
Qed.

(* --- the consequences (A..H), all derived from the one universal source/index exactness theorem. --- *)

(* A: a real source occurrence -> its metadata is stored. *)
Theorem source_occurrence_meta : forall f local o,
  source_occurrence_at f local = Some o ->
  Table.get local (table (build_file f)) = Some (occurrence_meta o).
Proof. intros f local o H. rewrite build_file_source_exact, H. reflexivity. Qed.

(* B: a stored entry -> exactly one source occurrence whose metadata it is. *)
Theorem meta_source_occurrence : forall f local m,
  Table.get local (table (build_file f)) = Some m ->
  exists o, source_occurrence_at f local = Some o /\ m = occurrence_meta o.
Proof.
  intros f local m H. rewrite build_file_source_exact in H.
  destruct (source_occurrence_at f local) as [o|] eqn:Eo; cbn [option_map] in H; [|discriminate].
  injection H as <-. exists o. split; reflexivity.
Qed.

(* C: absence both directions. *)
Theorem source_absence : forall f local,
  source_occurrence_at f local = None <->
  Table.get local (table (build_file f)) = None.
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
  exists m, Table.get local (table (build_file f)) = Some m /\ kind m = occurrence_kind o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_role_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ role m = occurrence_role o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_parent_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ parent m = occurrence_parent o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

Theorem source_subtree_end_exact : forall f local o,
  source_occurrence_at f local = Some o ->
  exists m, Table.get local (table (build_file f)) = Some m /\ subtree_end m = occurrence_subtree_end o.
Proof. intros f local o H. exists (occurrence_meta o). split; [apply source_occurrence_meta; exact H | reflexivity]. Qed.

(** ** PILLAR 2 — structural navigation invariants: preorder-interval ancestry,                 *)
(* exact parent lookup, interval-jump direct children, and canonical enumeration.  The [SubtreeWF] /  *)
(* [ForestWF] machinery below is GRAMMAR-AGNOSTIC (it speaks only of the node table + preorder         *)
(* intervals); it is reused unchanged from the accepted spike.  Only [build_*_spec] / [build_file_wf]  *)
(* (which relate the real builders to that machinery) and [root_id_canonical] are grammar-aware.  *)

(* preorder-interval ancestry: O(1) arithmetic on [subtree_end] after one map lookup. *)
Definition parent_id (t : Table.table Meta) (c : positive) : option positive :=
  match Table.get c t with Some m => parent m | None => None end.

Inductive Ancestor (t : Table.table Meta) : positive -> positive -> Prop :=
| Anc_dir  : forall a c, parent_id t c = Some a -> Ancestor t a c
| Anc_step : forall a p c, Ancestor t a p -> parent_id t c = Some p -> Ancestor t a c.

Definition is_ancestor_local (t : Table.table Meta) (a d : positive) : bool :=
  match Table.get a t with
  | Some ma => Pos.ltb a d && Pos.leb d (subtree_end ma)
  | None    => false
  end.

Fixpoint pos_seq (start : positive) (len : nat) : list positive :=
  match len with O => [] | S n => start :: pos_seq (Pos.succ start) n end.

(* direct children by INTERVAL JUMP: the cursor walks DIRECTLY from the first child to the
   parent's interval end, looking up ONLY the id at the cursor and, after each node, jumping the cursor PAST
   its whole subtree to [subtree_end+1] — it never constructs or traverses the skipped descendant ids.  So
   both the lookup count AND the number of recursive steps are O(#direct children), not O(#descendants). *)
Function child_enum (t : Table.table Meta) (pid limit cursor : positive)
    {measure (fun c => (S (Pos.to_nat limit) - Pos.to_nat c)%nat) cursor} : list positive :=
  if Pos.leb cursor limit then
    match Table.get cursor t with
    | Some mc =>
        let next := Pos.max (Pos.succ cursor) (Pos.succ (subtree_end mc)) in
        match parent mc with
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

Definition child_ids (t : Table.table Meta) (pid : positive) : list positive :=
  match Table.get pid t with
  | Some m => child_enum t pid (subtree_end m) (Pos.succ pid)
  | None => []
  end.

(* --- structural invariants of the built index (grammar-agnostic; verbatim from the accepted spike). --- *)

Definition Fresh (t : Table.table Meta) (from : positive) : Prop :=
  forall k, (from <= k)%positive -> Table.get k t = None.

Record SubtreeWF (t0 t : Table.table Meta) (oP : option positive) (me se : positive) : Prop := {
  sub_le    : (me <= se)%positive;
  sub_out   : forall k, (k < me)%positive \/ (se < k)%positive -> Table.get k t = Table.get k t0;
  sub_root  : exists m, Table.get me t = Some m /\ parent m = oP /\ subtree_end m = se;
  sub_pres  : forall k, (me <= k)%positive -> (k <= se)%positive -> Table.get k t <> None;
  sub_nest  : forall k m, (me <= k)%positive -> (k <= se)%positive -> Table.get k t = Some m ->
                (k <= subtree_end m)%positive /\ (subtree_end m <= se)%positive;
  sub_prng  : forall k m, (me < k)%positive -> (k <= se)%positive -> Table.get k t = Some m ->
                exists p mp, parent m = Some p /\ Table.get p t = Some mp /\
                  (me <= p)%positive /\ (p < k)%positive /\
                  (k <= subtree_end mp)%positive /\ (subtree_end m <= subtree_end mp)%positive;
  sub_snd   : forall a k ma, (me <= a)%positive -> (a <= se)%positive -> Table.get a t = Some ma ->
                (a < k)%positive -> (k <= subtree_end ma)%positive -> Ancestor t a k
}.

Arguments sub_le   {_ _ _ _ _}.
Arguments sub_out  {_ _ _ _ _}.
Arguments sub_root {_ _ _ _ _}.
Arguments sub_pres {_ _ _ _ _}.
Arguments sub_nest {_ _ _ _ _}.
Arguments sub_prng {_ _ _ _ _}.
Arguments sub_snd  {_ _ _ _ _}.

Record ForestWF (t0 t : Table.table Meta) (P lo nx : positive) : Prop := {
  for_le   : (lo <= nx)%positive;
  for_out  : forall k, (k < lo)%positive \/ (nx <= k)%positive -> Table.get k t = Table.get k t0;
  for_pres : forall k, (lo <= k)%positive -> (k < nx)%positive -> Table.get k t <> None;
  for_nest : forall k m, (lo <= k)%positive -> (k < nx)%positive -> Table.get k t = Some m ->
               (k <= subtree_end m)%positive /\ (subtree_end m < nx)%positive;
  for_prng : forall k m, (lo <= k)%positive -> (k < nx)%positive -> Table.get k t = Some m ->
               exists p, parent m = Some p /\
                 (p = P \/ ((lo <= p)%positive /\ (p < k)%positive /\
                            exists mp, Table.get p t = Some mp /\
                              (k <= subtree_end mp)%positive /\ (subtree_end m <= subtree_end mp)%positive));
  for_snd  : forall a k ma, (lo <= a)%positive -> (a < nx)%positive -> Table.get a t = Some ma ->
               (a < k)%positive -> (k <= subtree_end ma)%positive -> Ancestor t a k
}.

Arguments for_le   {_ _ _ _ _}.
Arguments for_out  {_ _ _ _ _}.
Arguments for_pres {_ _ _ _ _}.
Arguments for_nest {_ _ _ _ _}.
Arguments for_prng {_ _ _ _ _}.
Arguments for_snd  {_ _ _ _ _}.

Lemma ancestor_mono (t t' : Table.table Meta) :
  (forall j m, Table.get j t = Some m -> Table.get j t' = Some m) ->
  forall a c, Ancestor t a c -> Ancestor t' a c.
Proof.
  intros Hmono a c H; induction H as [a c Hp | a p c Hac IH Hp].
  - apply Anc_dir. unfold parent_id in *. destruct (Table.get c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
  - eapply Anc_step; [exact IH|].
    unfold parent_id in *. destruct (Table.get c t) as [m|] eqn:E; try discriminate.
    rewrite (Hmono _ _ E). exact Hp.
Qed.

Lemma forest_nil (t : Table.table Meta) P lo : ForestWF t t P lo lo.
Proof. constructor; intros; solve [ lia | reflexivity | exfalso; lia ]. Qed.

Lemma set_mono (tf : Table.table Meta) me meta :
  Table.get me tf = None -> forall j m, Table.get j tf = Some m -> Table.get j (Table.set me meta tf) = Some m.
Proof.
  intros Hfresh j m Hj. destruct (Pos.eq_dec j me) as [->|Hne].
  - rewrite Hfresh in Hj; discriminate.
  - rewrite Table.get_set_other by congruence. exact Hj.
Qed.

Lemma wrap_root_sound (t0 tf : Table.table Meta) me nx meta :
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  Table.get me tf = None ->
  forall k, me < k -> k < nx ->
    Ancestor (Table.set me meta tf) me k.
Proof.
  intros Hf0 HF Hfresh k.
  induction k as [k IHk] using (well_founded_induction (well_founded_ltof _ (fun p : positive => Pos.to_nat p))).
  intros Hmk Hkx.
  set (t := Table.set me meta tf).
  assert (Hget : Table.get k t = Table.get k tf).
  { unfold t; rewrite Table.get_set_other by lia; reflexivity. }
  destruct (Table.get k tf) as [m|] eqn:Em.
  2:{ exfalso. exact (for_pres HF k ltac:(lia) Hkx Em). }
  destruct (for_prng HF k m ltac:(lia) Hkx Em) as [p [Hpar Hcase]].
  assert (Hpid : parent_id t k = Some p).
  { unfold parent_id, t. rewrite Table.get_set_other by lia. rewrite Em. exact Hpar. }
  destruct Hcase as [Hp | [Hlo [Hpk _]]].
  - subst p. apply Anc_dir. exact Hpid.
  - eapply Anc_step; [ | exact Hpid].
    apply IHk.
    + unfold ltof. apply Pos2Nat.inj_lt. exact Hpk.
    + lia.
    + lia.
Qed.

Lemma subtree_from_forest (t0 tf : Table.table Meta) oP me se nx meta :
  nx = Pos.succ se ->
  Fresh t0 me ->
  ForestWF t0 tf me (Pos.succ me) nx ->
  Fresh tf nx ->
  parent meta = oP ->
  subtree_end meta = se ->
  Fresh (Table.set me meta tf) nx /\ SubtreeWF t0 (Table.set me meta tf) oP me se.
Proof.
  intros Hnx Hf0 HF Hff Hpar Hend.
  assert (Hmse : me <= se) by (generalize (for_le HF); lia).
  assert (Hfresh_me : Table.get me tf = None).
  { rewrite (for_out HF me) by lia. apply Hf0; lia. }
  set (t := Table.set me meta tf).
  assert (Hget_me : Table.get me t = Some meta) by (unfold t; apply Table.get_set_same).
  assert (Hget_ne : forall k, k <> me -> Table.get k t = Table.get k tf) by (intros; unfold t; apply Table.get_set_other; congruence).
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
        assert (Hmono : forall j mm, Table.get j tf = Some mm -> Table.get j t = Some mm)
          by (intros; unfold t; apply set_mono; assumption).
        eapply ancestor_mono; [exact Hmono|].
        eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
Qed.

Lemma forest_cons (t0 t1 t2 : Table.table Meta) P me se nx :
  SubtreeWF t0 t1 (Some P) me se ->
  Fresh t1 (Pos.succ se) ->
  ForestWF t1 t2 P (Pos.succ se) nx ->
  ForestWF t0 t2 P me nx.
Proof.
  intros HS Hf1 HF.
  assert (Hmse : me <= se) by (apply (sub_le HS)).
  assert (Hsx : Pos.succ se <= nx) by (apply (for_le HF)).
  assert (Hmono : forall j m, Table.get j t1 = Some m -> Table.get j t2 = Some m).
  { intros j m Hj. destruct (Pos.ltb j (Pos.succ se)) eqn:Hlt.
    - apply Pos.ltb_lt in Hlt. rewrite (for_out HF j) by lia. exact Hj.
    - apply Pos.ltb_ge in Hlt. rewrite (Hf1 j) in Hj by lia. discriminate. }
  assert (Hout2 : forall k, k < Pos.succ se \/ nx <= k -> Table.get k t2 = Table.get k t1)
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
      assert (Hmono2 : forall j mm, Table.get j t2 = Some mm -> Table.get j t2 = Some mm) by auto.
      eapply (for_snd HF); [lia|lia|exact Hget_a|exact Hak|exact Hkend].
    + apply Pos.leb_gt in Hge. rewrite Hout2 in Hget_a by lia.
      eapply ancestor_mono; [exact Hmono|].
      eapply (sub_snd HS); [lia|lia|exact Hget_a|exact Hak|].
      destruct (sub_nest HS a ma ltac:(lia) ltac:(lia) Hget_a) as [_ Hb]. lia.
Qed.

Lemma fresh_weaken (t : Table.table Meta) from from' :
  from <= from' -> Fresh t from -> Fresh t from'.
Proof. intros H HF k Hk. apply HF. lia. Qed.

Lemma fresh_empty (from : positive) : Fresh Table.empty from.
Proof. intros k _; apply Table.get_empty. Qed.

(* --- the real builders satisfy the WF machinery (grammar-aware). --- *)

Lemma build_expr_spec : forall e parent role me t0 t se,
  Fresh t0 me ->
  build_expr parent role me e t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me t0 t se Hf0 Hbuild; cbn [build_expr] in Hbuild;
    (* leaves: an empty children forest wrapped at [me] *)
    try (injection Hbuild as Ht Hse; subst t; subst se;
         eapply subtree_from_forest;
           [ reflexivity | exact Hf0 | apply forest_nil
           | (eapply fresh_weaken; [|exact Hf0]; lia) | reflexivity | reflexivity ]);
    (* conversion: a type-name leaf child at [me+1], then the operand subtree from [me+2] *)
    (destruct (build_expr me ConversionOperand (Pos.succ (Pos.succ me)) x
                (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t0))
       as [t1 e1] eqn:E1;
     injection Hbuild as Ht Hse; subst t; subst se;
     assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply fresh_weaken; [|exact Hf0]; lia);
     assert (Htn : Fresh (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t0) (Pos.succ (Pos.succ me))
                /\ SubtreeWF t0 (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t0) (Some me) (Pos.succ me) (Pos.succ me))
       by (eapply subtree_from_forest;
            [ reflexivity | exact Hf0' | apply forest_nil
            | (eapply fresh_weaken; [|exact Hf0]; lia) | reflexivity | reflexivity ]);
     destruct Htn as [Hfrtn HStn];
     destruct (IHx me ConversionOperand (Pos.succ (Pos.succ me))
                (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t0)
                t1 e1 Hfrtn E1) as [Hfr1 HS1];
     assert (HF : ForestWF t0 t1 me (Pos.succ me) (Pos.succ e1))
       by (eapply forest_cons; [ exact HStn | exact Hfrtn |
             eapply forest_cons; [ exact HS1 | exact Hfr1 | apply forest_nil ] ]);
     eapply subtree_from_forest;
       [ reflexivity | exact Hf0 | exact HF | exact Hfr1 | reflexivity | reflexivity ]).
Qed.

Lemma build_arg_spec : forall parent aidx me e t0 t se,
  Fresh t0 me ->
  build_arg parent aidx me e t0 = (t, se) ->
  Fresh t (Pos.succ se) /\ SubtreeWF t0 t (Some parent) me se.
Proof.
  intros parent aidx me e t0 t se Hf0 H. unfold build_arg in H.
  exact (build_expr_spec e parent (PrintlnArgument aidx) me t0 t se Hf0 H).
Qed.

Lemma build_seq_spec {X}
  (bx : positive -> nat -> positive -> X -> Table.table Meta -> Table.table Meta * positive) :
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
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply fresh_weaken; [|exact Hf0]; lia).
  destruct (build_seq_spec build_arg build_arg_spec args me 0 (Pos.succ me) t0 t1 nx1 Hf0' E1) as [Hfr1 HF1].
  assert (Hge : Pos.succ me <= nx1) by (apply (for_le HF1)).
  assert (Hnx : Pos.succ (Pos.pred nx1) = nx1)
    by (destruct (Pos.succ_pred_or nx1) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (Table.set me (MakeMeta StatementKind (Some parent) (DeclarationStatement sidx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (Table.set me (MakeMeta StatementKind (Some parent) (DeclarationStatement sidx) (Pos.pred nx1)) t1)
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
  assert (Hf0' : Fresh t0 (Pos.succ me)) by (eapply fresh_weaken; [|exact Hf0]; lia).
  destruct (build_seq_spec build_stmt build_stmt_spec body me 0 (Pos.succ me) t0 t1 nx1 Hf0' E1) as [Hfr1 HF1].
  assert (Hge : Pos.succ me <= nx1) by (apply (for_le HF1)).
  assert (Hnx : Pos.succ (Pos.pred nx1) = nx1)
    by (destruct (Pos.succ_pred_or nx1) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (Table.set me (MakeMeta DeclarationKind (Some parent) (FileDeclaration didx) (Pos.pred nx1)) t1) nx1 /\
              SubtreeWF t0 (Table.set me (MakeMeta DeclarationKind (Some parent) (FileDeclaration didx) (Pos.pred nx1)) t1)
                        (Some parent) me (Pos.pred nx1)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | exact Hf0 | exact HF1 | exact Hfr1 | reflexivity | reflexivity ]. }
  rewrite Hnx. exact H.
Qed.

Lemma build_file_wf (f : Syntax.File) :
  SubtreeWF Table.empty (table (build_file f)) None root_id (count (build_file f)).
Proof.
  unfold build_file. destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  set (pmeta := MakeMeta PackageClauseKind (Some root_id) FilePackage package_id).
  set (tp := Table.set package_id pmeta Table.empty).
  assert (HSpkg : Fresh tp (Pos.succ package_id) /\ SubtreeWF Table.empty tp (Some root_id) package_id package_id).
  { unfold tp, pmeta. eapply subtree_from_forest;
      [ reflexivity | apply fresh_empty | apply forest_nil | apply fresh_empty | reflexivity | reflexivity ]. }
  destruct HSpkg as [Hfrpkg HSpkg].
  destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) tp) as [t1 nx] eqn:E.
  cbn [table count].
  destruct (build_seq_spec build_decl build_decl_spec (Syntax.declarations f) root_id 0 (Pos.succ package_id)
              tp t1 nx Hfrpkg E) as [Hfr HFdecls].
  assert (HF : ForestWF Table.empty t1 root_id package_id nx)
    by (eapply forest_cons; [exact HSpkg | exact Hfrpkg | exact HFdecls]).
  assert (Hge : Pos.succ package_id <= nx) by (apply (for_le HFdecls)).
  assert (Hnx : Pos.succ (Pos.pred nx) = nx)
    by (destruct (Pos.succ_pred_or nx) as [->|H]; [exfalso; lia | exact H]).
  assert (H : Fresh (Table.set root_id (MakeMeta FileKind None FileRoot (Pos.pred nx)) t1) nx /\
              SubtreeWF Table.empty (Table.set root_id (MakeMeta FileKind None FileRoot (Pos.pred nx)) t1)
                        None root_id (Pos.pred nx)).
  { eapply subtree_from_forest;
      [ symmetry; exact Hnx | apply fresh_empty | exact HF | exact Hfr | reflexivity | reflexivity ]. }
  destruct H as [_ HS]. exact HS.
Qed.

(* --- enumeration helpers over the preorder id interval (grammar-agnostic; verbatim). --- *)

Lemma pos_seq_in (start c : positive) (len : nat) :
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

Lemma pos_seq_no_duplicates (start : positive) (len : nat) : NoDup (pos_seq start len).
Proof.
  revert start; induction len as [|n IH]; intros start; simpl.
  - constructor.
  - constructor; [| apply IH]. intro H. apply pos_seq_in in H. rewrite Pos2Nat.inj_succ in H. lia.
Qed.

(* --- the navigation theorem set; grammar-agnostic given [build_file_wf]. --- *)

Lemma in_domain (f : Syntax.File) k m :
  Table.get k (table (build_file f)) = Some m ->
  root_id <= k /\ k <= count (build_file f).
Proof.
  intros H. pose proof (build_file_wf f) as WF. split.
  - destruct (Pos.leb root_id k) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (left; lia).
    rewrite Table.get_empty in H; discriminate.
  - destruct (Pos.leb k (count (build_file f))) eqn:E; [apply Pos.leb_le; exact E|].
    apply Pos.leb_gt in E. rewrite (sub_out WF k) in H by (right; lia).
    rewrite Table.get_empty in H; discriminate.
Qed.

(* the root id is canonical: every file root occupies the SAME fixed local id [root_id]. *)
Theorem root_id_canonical (f : Syntax.File) :
  exists m, Table.get root_id (table (build_file f)) = Some m /\ kind m = FileKind /\ role m = FileRoot.
Proof.
  unfold build_file. destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  destruct (build_seq build_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f)
              (Table.set package_id (MakeMeta PackageClauseKind (Some root_id) FilePackage package_id) Table.empty))
    as [t1 nx] eqn:E.
  exists (MakeMeta FileKind None FileRoot (Pos.pred nx)).
  cbn [table]. rewrite Table.get_set_same. split; [reflexivity | split; reflexivity].
Qed.

(* the root has no parent, and ONLY the root has no parent. *)
Theorem root_no_parent (f : Syntax.File) m :
  Table.get root_id (table (build_file f)) = Some m -> parent m = None.
Proof.
  intros H. pose proof (build_file_wf f) as WF. destruct (sub_root WF) as [m0 [Hg [Hp _]]].
  rewrite Hg in H. injection H as <-. exact Hp.
Qed.

Theorem nonroot_has_parent (f : Syntax.File) k m :
  Table.get k (table (build_file f)) = Some m -> k <> root_id -> exists p, parent m = Some p.
Proof.
  intros H Hne. pose proof (build_file_wf f) as WF.
  destruct (in_domain f k m H) as [Hlo Hhi].
  assert (root_id < k) by lia.
  destruct (sub_prng WF k m ltac:(lia) Hhi H) as [p [mp [Hpar _]]]. exists p; exact Hpar.
Qed.

Theorem parent_unique (f : Syntax.File) k m p1 p2 :
  Table.get k (table (build_file f)) = Some m -> parent m = Some p1 -> parent m = Some p2 -> p1 = p2.
Proof. intros _ H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(* (completeness half) — ancestry implies nested preorder intervals. *)
Lemma ancestor_complete (f : Syntax.File) a d :
  Ancestor (table (build_file f)) a d ->
  exists ma md, Table.get a (table (build_file f)) = Some ma /\
                Table.get d (table (build_file f)) = Some md /\
                a < d /\ d <= subtree_end ma /\ subtree_end md <= subtree_end ma.
Proof.
  pose proof (build_file_wf f) as WF.
  set (t := table (build_file f)) in *.
  induction 1 as [a d Hp | a p c Hac IH Hp].
  - unfold parent_id in Hp. destruct (Table.get d t) as [md|] eqn:Ed; [|discriminate].
    destruct (in_domain f d md Ed) as [Hlo Hhi].
    assert (Hdne : d <> root_id).
    { intro; subst d. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ed; injection Ed as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF d md ltac:(lia) Hhi Ed) as [p [mp [Hpar [Hmp [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-.
    exists mp, md. repeat split; try assumption; lia.
  - unfold parent_id in Hp. destruct (Table.get c t) as [mc|] eqn:Ec; [|discriminate].
    destruct IH as [ma [mp0 [Hga [Hgp [Hap [Hpend Hmpend]]]]]].
    destruct (in_domain f c mc Ec) as [Hlo Hhi].
    assert (Hcne : c <> root_id).
    { intro; subst c. destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. rewrite Hg in Ec; injection Ec as <-.
      rewrite Hp0 in Hp; discriminate. }
    destruct (sub_prng WF c mc ltac:(lia) Hhi Ec) as [p' [mp' [Hpar [Hmp' [Hle1 [Hlt1 [Hb1 Hb2]]]]]]].
    rewrite Hp in Hpar. injection Hpar as <-. rewrite Hgp in Hmp'. injection Hmp' as <-.
    exists ma, mc. repeat split; try assumption; lia.
Qed.

Definition parentb (t : Table.table Meta) (c pid : positive) : bool :=
  match Table.get c t with
  | Some mc => match parent mc with Some p => Pos.eqb p pid | None => false end
  | None => false
  end.

Lemma ancestor_parent_ge (f : Syntax.File) a d p :
  Ancestor (table (build_file f)) a d ->
  parent_id (table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Hanc Hp. inversion Hanc; subst.
  - rewrite H in Hp. injection Hp as <-. lia.
  - rewrite H0 in Hp. injection Hp as <-.
    destruct (ancestor_complete f a _ H) as [ma [md [_ [_ [Hlt _]]]]]. lia.
Qed.

Lemma desc_parent_ge (f : Syntax.File) a ma d p :
  Table.get a (table (build_file f)) = Some ma ->
  (a < d)%positive -> (d <= subtree_end ma)%positive ->
  parent_id (table (build_file f)) d = Some p -> (a <= p)%positive.
Proof.
  intros Ha Hlt Hle Hp. pose proof (build_file_wf f) as WF.
  destruct (in_domain f a ma Ha) as [Hlo Hhi].
  eapply ancestor_parent_ge; [ eapply (sub_snd WF a d ma); [lia|lia|exact Ha|exact Hlt|exact Hle] | exact Hp ].
Qed.

Lemma child_gt (f : Syntax.File) pid c mc :
  Table.get c (table (build_file f)) = Some mc -> parent mc = Some pid ->
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

Lemma first_child (f : Syntax.File) pid mp :
  Table.get pid (table (build_file f)) = Some mp ->
  (pid < subtree_end mp)%positive ->
  parent_id (table (build_file f)) (Pos.succ pid) = Some pid.
Proof.
  intros Hpid Hlt. pose proof (build_file_wf f) as WF.
  destruct (in_domain f pid mp Hpid) as [Hlo Hhi].
  destruct (sub_nest WF pid mp Hlo Hhi Hpid) as [_ Hmpcnt].
  assert (Hpres : Table.get (Pos.succ pid) (table (build_file f)) <> None)
    by (eapply (sub_pres WF (Pos.succ pid)); lia).
  destruct (Table.get (Pos.succ pid) (table (build_file f))) as [m1|] eqn:E1; [|contradiction].
  destruct (sub_prng WF (Pos.succ pid) m1 ltac:(lia) ltac:(lia) E1) as [p [mp2 [Hpar [_ [_ [Hltp _]]]]]].
  assert (Hpge : (pid <= p)%positive)
    by (eapply (desc_parent_ge f pid mp (Pos.succ pid) p Hpid); [lia|lia|unfold parent_id; rewrite E1; exact Hpar]).
  unfold parent_id. rewrite E1. rewrite Hpar. f_equal. lia.
Qed.

Lemma next_child (f : Syntax.File) pid mp c mc :
  Table.get pid (table (build_file f)) = Some mp ->
  Table.get c (table (build_file f)) = Some mc -> parent mc = Some pid ->
  (subtree_end mc < subtree_end mp)%positive ->
  parent_id (table (build_file f)) (Pos.succ (subtree_end mc)) = Some pid.
Proof.
  intros Hpid Hc Hpar HEc. pose proof (build_file_wf f) as WF.
  pose proof (child_gt f pid c mc Hc Hpar) as Hpc.
  destruct (in_domain f pid mp Hpid) as [Hlo_pid Hhi_pid].
  destruct (in_domain f c mc Hc) as [Hlo_c Hhi_c].
  destruct (sub_nest WF c mc ltac:(lia) Hhi_c Hc) as [Hc_le _].
  destruct (sub_nest WF pid mp Hlo_pid Hhi_pid Hpid) as [_ Hmpcnt].
  set (d := Pos.succ (subtree_end mc)).
  assert (Hd1 : (pid < d)%positive) by (unfold d; lia).
  assert (Hd2 : (d <= subtree_end mp)%positive) by (unfold d; lia).
  assert (Hpres : Table.get d (table (build_file f)) <> None) by (eapply (sub_pres WF d); lia).
  destruct (Table.get d (table (build_file f))) as [md|] eqn:Ed; [|contradiction].
  destruct (sub_prng WF d md ltac:(lia) ltac:(lia) Ed) as [p [mpp [Hparp [Hgetp [_ [Hltp [Hb1 _]]]]]]].
  assert (Hpge : (pid <= p)%positive)
    by (eapply (desc_parent_ge f pid mp d p Hpid); [lia|lia|unfold parent_id; rewrite Ed; exact Hparp]).
  destruct (in_domain f p mpp Hgetp) as [Hlop Hhip].
  assert (Hp_eq : p = pid).
  { destruct (Pos.eq_dec p pid) as [->|Hne]; [reflexivity|]. exfalso.
    assert (Hpgt : (pid < p)%positive) by lia.
    destruct (Pos.leb c p) eqn:Hcp.
    - apply Pos.leb_le in Hcp.
      assert (Hpsub : (subtree_end mpp <= subtree_end mc)%positive).
      { destruct (Pos.eq_dec p c) as [->|Hpc2].
        - rewrite Hgetp in Hc. injection Hc as <-. lia.
        - destruct (ancestor_complete f c p (sub_snd WF c p mc ltac:(lia) Hhi_c Hc ltac:(lia) ltac:(lia)))
            as [mc' [mpp' [Hgc [Hgp [_ [_ Hend]]]]]].
          rewrite Hc in Hgc; injection Hgc as <-. rewrite Hgetp in Hgp; injection Hgp as <-. lia. }
      unfold d in Hb1. lia.
    - apply Pos.leb_gt in Hcp.
      assert (Hcanc : Ancestor (table (build_file f)) p c).
      { eapply (sub_snd WF p c mpp); [lia|exact Hhip|exact Hgetp|lia|]. unfold d in Hb1. lia. }
      assert (p <= pid)%positive by (eapply ancestor_parent_ge; [exact Hcanc | unfold parent_id; rewrite Hc; exact Hpar]).
      lia. }
  unfold parent_id. rewrite Ed. rewrite Hparp. rewrite Hp_eq. reflexivity.
Qed.

Lemma interior_not_child (f : Syntax.File) pid cur mcur k :
  Table.get cur (table (build_file f)) = Some mcur -> parent mcur = Some pid ->
  (cur < k)%positive -> (k <= subtree_end mcur)%positive ->
  parentb (table (build_file f)) k pid = false.
Proof.
  intros Hcur Hpar Hlt Hle. pose proof (child_gt f pid cur mcur Hcur Hpar) as Hpc.
  unfold parentb. destruct (Table.get k (table (build_file f))) as [mk|] eqn:Ek; [|reflexivity].
  destruct (parent mk) as [q|] eqn:Eq; [|reflexivity].
  assert (cur <= q)%positive
    by (eapply (desc_parent_ge f cur mcur k q Hcur); [lia|lia|unfold parent_id; rewrite Ek; exact Eq]).
  destruct (Pos.eqb q pid) eqn:Eqp; [apply Pos.eqb_eq in Eqp; lia | reflexivity].
Qed.

Lemma built_nested (f : Syntax.File) x mx :
  Table.get x (table (build_file f)) = Some mx -> (x <= subtree_end mx)%positive.
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
    pose proof (Pos.le_max_l (Pos.succ cursor) (Pos.succ (subtree_end mc))) as Hm.
  - apply in_inv in Hin. destruct Hin as [Heq|Hin]; [subst c; lia|]. apply IHl in Hin. lia.
  - apply IHl in Hin. lia.
  - apply IHl in Hin. lia.
Qed.

Lemma child_enum_strongly_sorted : forall t pid limit cursor,
  StronglySorted Pos.lt (child_enum t pid limit cursor).
Proof.
  intros t pid limit cursor.
  functional induction (child_enum t pid limit cursor); try (solve [constructor]); try exact IHl.
  constructor; [exact IHl|].
  apply Forall_forall. intros y Hy. apply child_enum_ge in Hy.
  pose proof (Pos.le_max_l (Pos.succ cursor) (Pos.succ (subtree_end mc))). lia.
Qed.

Lemma child_enum_reaches : forall N f pid mp cur mcur c mc,
  Table.get pid (table (build_file f)) = Some mp ->
  Table.get cur (table (build_file f)) = Some mcur -> parent mcur = Some pid ->
  Table.get c  (table (build_file f)) = Some mc  -> parent mc  = Some pid ->
  (cur <= c)%positive -> (c <= subtree_end mp)%positive ->
  N = (S (Pos.to_nat (subtree_end mp)) - Pos.to_nat cur)%nat ->
  In c (child_enum (table (build_file f)) pid (subtree_end mp) cur).
Proof.
  induction N as [N IH] using (well_founded_induction lt_wf).
  intros f pid mp cur mcur c mc Hpid Hcur Hpar Hc Hpc Hle Hcend HN.
  rewrite child_enum_equation.
  destruct (Pos.leb cur (subtree_end mp)) eqn:Hleb; [|apply Pos.leb_gt in Hleb; exfalso; lia].
  rewrite Hcur. cbn iota beta zeta. rewrite Hpar. cbn iota beta zeta. rewrite Pos.eqb_refl.
  destruct (Pos.eq_dec c cur) as [->|Hcne]; [left; reflexivity|].
  right.
  assert (Hcurlt : (cur < c)%positive) by lia.
  assert (HEcur : (subtree_end mcur < c)%positive).
  { destruct (Pos.leb c (subtree_end mcur)) eqn:Hb; [|apply Pos.leb_gt in Hb; lia].
    apply Pos.leb_le in Hb. exfalso.
    pose proof (interior_not_child f pid cur mcur c Hcur Hpar Hcurlt Hb) as Hnc.
    assert (parentb (table (build_file f)) c pid = true)
      by (unfold parentb; rewrite Hc; cbn; rewrite Hpc; cbn; apply Pos.eqb_refl).
    congruence. }
  assert (Hcur_le_Ecur : (cur <= subtree_end mcur)%positive) by (apply built_nested in Hcur; exact Hcur).
  rewrite (Pos.max_r (Pos.succ cur) (Pos.succ (subtree_end mcur))) by lia.
  assert (HEcE : (subtree_end mcur < subtree_end mp)%positive) by lia.
  pose proof (next_child f pid mp cur mcur Hpid Hcur Hpar HEcE) as Hnext. unfold parent_id in Hnext.
  destruct (Table.get (Pos.succ (subtree_end mcur)) (table (build_file f))) as [mnc|] eqn:Enc;
    [|discriminate].
  eapply (IH (S (Pos.to_nat (subtree_end mp)) - Pos.to_nat (Pos.succ (subtree_end mcur)))%nat);
    [ rewrite HN, Pos2Nat.inj_succ;
      assert (Pos.to_nat cur <= Pos.to_nat (subtree_end mcur))%nat by (apply Pos2Nat.inj_le; exact Hcur_le_Ecur);
      lia
    | exact Hpid | exact Enc | exact Hnext | exact Hc | exact Hpc | lia | exact Hcend | reflexivity ].
Qed.

(* the O(1) preorder-interval ancestor test is sound AND complete. *)
Theorem interval_ancestry (f : Syntax.File) a d :
  Table.get a (table (build_file f)) <> None ->
  (is_ancestor_local (table (build_file f)) a d = true <-> Ancestor (table (build_file f)) a d).
Proof.
  intros Ha. pose proof (build_file_wf f) as WF.
  set (t := table (build_file f)) in *.
  unfold is_ancestor_local. destruct (Table.get a t) as [ma|] eqn:Ea; [|congruence].
  split.
  - intros Hb. apply andb_true_iff in Hb as [H1 H2].
    apply Pos.ltb_lt in H1. apply Pos.leb_le in H2.
    destruct (in_domain f a ma Ea) as [Hlo Hhi].
    eapply (sub_snd WF); [lia|exact Hhi|exact Ea|exact H1|exact H2].
  - intros Hanc. destruct (ancestor_complete f a d Hanc) as [ma' [md [Hga [_ [Had [Hdend _]]]]]].
    unfold t in Ea. assert (ma = ma') by congruence. subst ma'.
    apply andb_true_iff; split; [apply Pos.ltb_lt; lia | apply Pos.leb_le; lia].
Qed.

(* (children source order). *)
Theorem children_sorted (f : Syntax.File) p :
  StronglySorted Pos.lt (child_ids (table (build_file f)) p).
Proof.
  unfold child_ids. destruct (Table.get p (table (build_file f))) as [m|] eqn:Ep; [|constructor].
  apply child_enum_strongly_sorted.
Qed.

(* parent/child are inverse (interval-jump enumeration is sound + complete). *)
Theorem child_has_parent (f : Syntax.File) p c :
  In c (child_ids (table (build_file f)) p) -> parent_id (table (build_file f)) c = Some p.
Proof.
  unfold child_ids. destruct (Table.get p (table (build_file f))) as [mp|] eqn:Ep; [|intros []].
  apply child_enum_sound.
Qed.

Theorem parent_has_child (f : Syntax.File) p c mc :
  Table.get c (table (build_file f)) = Some mc -> parent mc = Some p ->
  In c (child_ids (table (build_file f)) p).
Proof.
  intros Hc Hpar. pose proof (build_file_wf f) as WF.
  pose proof (child_gt f p c mc Hc Hpar) as Hpc.
  destruct (in_domain f c mc Hc) as [Hlo Hhi].
  assert (Hcne : c <> root_id)
    by (intro; subst c; destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]; rewrite Hg in Hc; injection Hc as <-;
        rewrite Hp0 in Hpar; discriminate).
  destruct (sub_prng WF c mc ltac:(lia) Hhi Hc) as [p' [mp' [Hpar' [Hgp [_ [_ [Hcbound _]]]]]]].
  rewrite Hpar in Hpar'. injection Hpar' as <-.
  assert (HpE : (p < subtree_end mp')%positive) by lia.
  pose proof (first_child f p mp' Hgp HpE) as Hfc. unfold parent_id in Hfc.
  destruct (Table.get (Pos.succ p) (table (build_file f))) as [m1|] eqn:E1; [|discriminate].
  unfold child_ids. rewrite Hgp.
  eapply (child_enum_reaches _ f p mp' (Pos.succ p) m1 c mc);
    [ exact Hgp | exact E1 | exact Hfc | exact Hc | exact Hpar | lia | exact Hcbound | reflexivity ].
Qed.

(* every occurrence appears EXACTLY ONCE in canonical preorder enumeration. *)
Definition all_ids (fi : File) : list positive := pos_seq root_id (Pos.to_nat (count fi)).

Theorem enumeration_nodup (f : Syntax.File) : NoDup (all_ids (build_file f)).
Proof. apply pos_seq_no_duplicates. Qed.

Theorem enumeration_complete (f : Syntax.File) k m :
  Table.get k (table (build_file f)) = Some m -> In k (all_ids (build_file f)).
Proof.
  intros H. destruct (in_domain f k m H) as [Hlo Hhi]. unfold all_ids.
  apply pos_seq_in. unfold root_id. rewrite Pos2Nat.inj_1.
  assert (Pos.to_nat k <= Pos.to_nat (count (build_file f)))%nat by (apply Pos2Nat.inj_le; exact Hhi).
  assert (1 <= Pos.to_nat k)%nat by (pose proof (Pos2Nat.is_pos k); lia).
  lia.
Qed.

Theorem enumeration_sound (f : Syntax.File) k :
  In k (all_ids (build_file f)) -> Table.get k (table (build_file f)) <> None.
Proof.
  unfold all_ids. intros Hin. apply pos_seq_in in Hin. unfold root_id in Hin. rewrite Pos2Nat.inj_1 in Hin.
  pose proof (build_file_wf f) as WF. apply (sub_pres WF).
  - unfold root_id. apply Pos2Nat.inj_le. rewrite Pos2Nat.inj_1. lia.
  - apply Pos2Nat.inj_le. lia.
Qed.

(* the builder branches only on tree SHAPE, and metadata is not a subtree copy. *)
Fixpoint same_shape (e1 e2 : Syntax.Expr) : Prop :=
  match e1, e2 with
  | Syntax.Convert _ x1, Syntax.Convert _ x2 => same_shape x1 x2
  | Syntax.BoolLiteral _, Syntax.BoolLiteral _ => True
  | Syntax.IntegerLiteral _, Syntax.IntegerLiteral _ => True
  | Syntax.NegatedIntegerLiteral _, Syntax.NegatedIntegerLiteral _ => True
  | Syntax.StringLiteral _, Syntax.StringLiteral _ => True
  | Syntax.FloatLiteral _, Syntax.FloatLiteral _ => True
  | Syntax.ComplexLiteral _, Syntax.ComplexLiteral _ => True
  | _, _ => False
  end.

(* two expressions of the same SHAPE (ignoring every leaf payload and every conversion type tag) build to
   the IDENTICAL table — so the builder cannot be comparing / deduplicating subtrees by their content. *)
Theorem builder_no_structural_search :
  forall e1 e2 parent role me t,
    same_shape e1 e2 -> build_expr parent role me e1 t = build_expr parent role me e2 t.
Proof.
  induction e1 as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros [ b2 | n1' | n2' | s2 | df2 | dcx2 | ts2 x2 ] parent role me t Hsh;
    cbn [same_shape] in Hsh; try contradiction; try reflexivity;
    (cbn [build_expr];
     rewrite (IHx x2 me ConversionOperand (Pos.succ (Pos.succ me))
                (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t) Hsh);
     destruct (build_expr me ConversionOperand (Pos.succ (Pos.succ me)) x2
                (Table.set (Pos.succ me) (MakeMeta TypeNameKind (Some me) ConversionTarget (Pos.succ me)) t))
       as [t1 e1]; reflexivity).
Qed.

Theorem meta_stores_no_subtree :
  forall m : Meta, exists k op r e,
    m = MakeMeta k op r e /\ (forall e', MakeMeta k op r e = MakeMeta k op r e' -> e = e').
Proof. intros [k op r e]. exists k, op, r, e. split; [reflexivity|]. intros e' H; injection H as <-; reflexivity. Qed.

(** ** PILLAR 3 — snapshot-indexed references over the exact [Syntax.Program].                        *)
(* A reference belongs to the EXACT immutable program snapshot [p] (it is indexed by [p]), never to  *)
(* free-standing index data — so two programs sharing a file map but differing in [ModuleSpec], or    *)
(* sharing a shape but differing in payload, have NON-INTERCHANGEABLE reference types.  Structurally  *)
(* guaranteed queries are TOTAL; only [parent_of] is optional (a file root has no parent).            *)

(* decidable equality for the raw syntax (for UIP over the reference proof fields). *)
Definition float_decimal_eq_dec (a b : Float.Decimal) : {a = b} + {a <> b}.
Proof.
  destruct (Float.decimal_equalb a b) eqn:E; [ left; apply Float.decimal_equalb_spec; exact E | right ].
  intro H; subst; rewrite (proj2 (Float.decimal_equalb_spec b b) eq_refl) in E; discriminate.
Defined.
Definition complex_decimal_eq_dec (a b : Complex.Decimal) : {a = b} + {a <> b}.
Proof. decide equality; apply float_decimal_eq_dec. Defined.
Definition supported_type_eq_dec (a b : Names.SupportedType) : {a = b} + {a <> b}.
Proof.
  destruct (Names.supported_equalb a b) eqn:E; [left; apply Names.supported_equalb_spec; exact E|right].
  intro H; subst; rewrite (proj2 (Names.supported_equalb_spec b b) eq_refl) in E; discriminate.
Defined.
Definition type_expr_eq_dec (a b : Syntax.TypeExpr) : {a = b} + {a <> b}.
Proof.
  destruct a as [[sa]]; destruct b as [[sb]];
    destruct (supported_type_eq_dec sa sb) as [->|Hne];
    [ left; reflexivity | right; intro H; injection H as ->; apply Hne; reflexivity ].
Defined.
Definition expression_eq_dec (a b : Syntax.Expr) : {a = b} + {a <> b}.
Proof.
  decide equality;
    first [ apply Bool.bool_dec | apply N.eq_dec | apply string_dec
          | apply type_expr_eq_dec
          | apply float_decimal_eq_dec | apply complex_decimal_eq_dec ].
Defined.
Definition statement_eq_dec (a b : Syntax.Stmt) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec expression_eq_dec). Defined.
Definition declaration_eq_dec (a b : Syntax.Decl) : {a = b} + {a <> b}.
Proof. decide equality; apply (list_eq_dec statement_eq_dec). Defined.
Definition package_clause_eq_dec (a b : Syntax.PackageClause) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition import_spec_eq_dec (a b : Syntax.ImportSpec) : {a = b} + {a <> b}.
Proof. destruct a. Defined.
Definition source_file_eq_dec (a b : Syntax.File) : {a = b} + {a <> b}.
Proof.
  decide equality;
    first [ apply (list_eq_dec declaration_eq_dec) | apply (list_eq_dec import_spec_eq_dec)
          | apply package_clause_eq_dec ].
Defined.
Definition optional_source_file_eq_dec (a b : option Syntax.File) : {a = b} + {a <> b}.
Proof. decide equality; apply source_file_eq_dec. Defined.

Lemma file_path_eq_dec (a b : FilePath.T) : {a = b} + {a <> b}.
Proof.
  destruct (FilePath.equalb a b) eqn:E; [left; apply FilePath.equalb_spec; exact E|].
  right; intro Heq; subst; rewrite (proj2 (FilePath.equalb_spec b b) eq_refl) in E; discriminate.
Qed.

(* the outer program index: a STANDARD FilePath.T map [FileMap.t File] keyed DIRECTLY by path — the
   standard [map] of [build_file] over the program's source files, so ONE map lookup reaches a file's index. *)
Module FileMap := Collections.FileMap.
Module FileFacts := Collections.FileFacts.
Definition outer_of (fm : Syntax.Files) : FileMap.t File := FileMap.map build_file fm.
Lemma outer_get_exact : forall fm path,
  FileMap.find path (outer_of fm)
  = match FileMap.find path fm with Some f => Some (build_file f) | None => None end.
Proof. intros fm path. unfold outer_of. rewrite FileFacts.map_o. destruct (FileMap.find path fm); reflexivity. Qed.
Lemma outer_get_at : forall fm path f,
  FileMap.find path fm = Some f -> FileMap.find path (outer_of fm) = Some (build_file f).
Proof. intros fm path f H. rewrite outer_get_exact, H. reflexivity. Qed.

(* a local id is a real occurrence of file [f] iff it resolves in [f]'s built per-file table. *)
Definition valid_localb (f : Syntax.File) (local : positive) : bool :=
  match Table.get local (table (build_file f)) with Some _ => true | None => false end.

(* the public raw occurrence key: file PATH (the map-key identity) + file-local preorder id. *)
Record Key := MakeKey { key_path : FilePath.T ; key_local : positive }.
Definition key_equalb (a b : Key) : bool :=
  FilePath.equalb (key_path a) (key_path b) && Pos.eqb (key_local a) (key_local b).

Theorem key_eq_dec (a b : Key) : {a = b} + {a <> b}.
Proof.
  destruct a as [fa la], b as [fb lb].
  destruct (file_path_eq_dec fa fb) as [->|Hf]; [| right; intro H; injection H as <- <-; apply Hf; reflexivity].
  destruct (Pos.eq_dec la lb) as [->|Hl]; [left; reflexivity|].
  right; intro H; injection H as <-; apply Hl; reflexivity.
Qed.

Theorem key_equalb_spec (a b : Key) : key_equalb a b = true <-> a = b.
Proof.
  unfold key_equalb. rewrite andb_true_iff. split.
  - intros [Hf Hl]. apply FilePath.equalb_spec in Hf. apply Pos.eqb_eq in Hl.
    destruct a, b; simpl in *; subst; reflexivity.
  - intros ->. split; [apply FilePath.equalb_spec; reflexivity | apply Pos.eqb_eq; reflexivity].
Qed.

(* a child id of any node is a real occurrence — used to build validated child references without drops. *)
Lemma child_ids_parent (t : Table.table Meta) (pid c : positive) :
  In c (child_ids t pid) -> parent_id t c = Some pid.
Proof. unfold child_ids. destruct (Table.get pid t) as [m|]; [|intros []]. apply child_enum_sound. Qed.

(* the canonical preorder id enumeration [pos_seq] is strictly increasing (source order). *)
Lemma pos_seq_sorted (start : positive) (len : nat) : StronglySorted Pos.lt (pos_seq start len).
Proof.
  revert start; induction len as [|n IH]; intros start; cbn [pos_seq]; [constructor|].
  constructor; [apply IH|]. apply Forall_forall. intros y Hy. apply pos_seq_in in Hy.
  rewrite Pos2Nat.inj_succ in Hy. apply Pos2Nat.inj_lt. lia.
Qed.

(* every file has a root occurrence at [root_id], so the root is always a valid local id. *)
Lemma root_valid (f : Syntax.File) : valid_localb f root_id = true.
Proof. unfold valid_localb. destruct (root_id_canonical f) as [m [Hg _]]. rewrite Hg. reflexivity. Qed.

(* every id in the canonical enumeration of a file is a valid occurrence of it (no drops). *)
Lemma all_ids_valid (f : Syntax.File) :
  forall c, In c (all_ids (build_file f)) -> valid_localb f c = true.
Proof.
  intros c Hin. unfold valid_localb.
  destruct (Table.get c (table (build_file f))) eqn:E; [reflexivity|].
  exfalso. exact (enumeration_sound f c Hin E).
Qed.

Lemma next_decls_ge : forall ds me, (me <= next_decls me ds)%positive.
Proof.
  induction ds as [|d rest IH]; intros me; cbn [next_decls]; [lia|].
  specialize (IH (Pos.succ (end_decl me d))). pose proof (end_decl_ge d me) as Hd. lia.
Qed.

(** ** the canonical INDEXED TRAVERSAL foundation: a structural, one-pass occurrence-emitting fold. *)
(* [occurrences_file] walks the ORIGINAL source forest in canonical preorder and emits, for every occurrence, *)
(* its local id paired with its exact [Occurrence] (which carries the original syntax VIEW) — the *)
(* fragment is produced by the ONE structural pass, never recovered per node.  It is proved EXACT       *)
(* against the independent [source_occurrence_at] spec (a listed pair IS that spec's occurrence, and    *)
(* every occurrence is listed), and its ids are strictly increasing (canonical source order).  The      *)
(* reference-level traversal (which mints the validated [NodeRef] at each position) is in [Snapshot] below. *)

Fixpoint occurrences_expr (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr)
  : list (positive * Occurrence) :=
  match e with
  | Syntax.BoolLiteral _ | Syntax.IntegerLiteral _ | Syntax.NegatedIntegerLiteral _ | Syntax.StringLiteral _ | Syntax.FloatLiteral _ | Syntax.ComplexLiteral _ =>
      [(me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role me)]
  | Syntax.Convert ts x =>
      (me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (end_expr me e))
        :: (Pos.succ me, MakeOccurrence TypeNameKind (TypeNameView ts) (Some me) ConversionTarget (Pos.succ me))
        :: occurrences_expr me ConversionOperand (Pos.succ (Pos.succ me)) x
  end.
Definition occurrences_arg (parent : positive) (aidx : nat) (me : positive) (e : Syntax.Expr) : list (positive * Occurrence) :=
  occurrences_expr parent (PrintlnArgument aidx) me e.
Fixpoint occurrences_args (parent : positive) (aidx : nat) (me : positive) (es : list Syntax.Expr) : list (positive * Occurrence) :=
  match es with
  | [] => []
  | e :: rest => occurrences_arg parent aidx me e ++ occurrences_args parent (S aidx) (Pos.succ (end_expr me e)) rest
  end.
Definition occurrences_stmt (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt) : list (positive * Occurrence) :=
  match s with
  | Syntax.Println args =>
      (me, MakeOccurrence StatementKind (StatementView s) (Some parent) (DeclarationStatement sidx) (end_stmt me s))
        :: occurrences_args me 0 (Pos.succ me) args
  end.
Fixpoint occurrences_stmts (parent : positive) (sidx : nat) (me : positive) (ss : list Syntax.Stmt) : list (positive * Occurrence) :=
  match ss with
  | [] => []
  | s :: rest => occurrences_stmt parent sidx me s ++ occurrences_stmts parent (S sidx) (Pos.succ (end_stmt me s)) rest
  end.
Definition occurrences_decl (parent : positive) (didx : nat) (me : positive) (d : Syntax.Decl) : list (positive * Occurrence) :=
  match d with
  | Syntax.Main body =>
      (me, MakeOccurrence DeclarationKind (DeclarationView d) (Some parent) (FileDeclaration didx) (end_decl me d))
        :: occurrences_stmts me 0 (Pos.succ me) body
  end.
Fixpoint occurrences_decls (parent : positive) (didx : nat) (me : positive) (ds : list Syntax.Decl) : list (positive * Occurrence) :=
  match ds with
  | [] => []
  | d :: rest => occurrences_decl parent didx me d ++ occurrences_decls parent (S didx) (Pos.succ (end_decl me d)) rest
  end.
Definition occurrences_file (f : Syntax.File) : list (positive * Occurrence) :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      (root_id, MakeOccurrence FileKind (FileView f) None FileRoot (count_file f))
        :: (package_id, MakeOccurrence PackageClauseKind (PackageClauseView (Syntax.package f)) (Some root_id) FilePackage package_id)
        :: occurrences_decls root_id 0 (Pos.succ package_id) (Syntax.declarations f)
  end.

(* --- interval-bound lemmas: an emitted id lies within its subtree / run window. --- *)

Lemma occurrences_expr_ge : forall e parent role me id occ,
  In (id, occ) (occurrences_expr parent role me e) -> (me <= id)%positive.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me id occ Hin; cbn [occurrences_expr] in Hin;
    try (destruct Hin as [Heq|[]]; injection Heq as <- <-; lia);
    (destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|];
     destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|];
     specialize (IHx me ConversionOperand (Pos.succ (Pos.succ me)) id occ Hin); lia).
Qed.

Lemma occurrences_expr_le : forall e parent role me id occ,
  In (id, occ) (occurrences_expr parent role me e) -> (id <= end_expr me e)%positive.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me id occ Hin; cbn [occurrences_expr end_expr] in *;
    try (destruct Hin as [Heq|[]]; injection Heq as <- <-; lia);
    (pose proof (end_expr_ge x (Pos.succ (Pos.succ me))) as Hx;
     destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|];
     destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|];
     apply (IHx me ConversionOperand (Pos.succ (Pos.succ me)) id occ Hin)).
Qed.

Lemma occurrences_args_ge : forall es parent aidx me id occ,
  In (id, occ) (occurrences_args parent aidx me es) -> (me <= id)%positive.
Proof.
  induction es as [|e rest IH]; intros parent aidx me id occ Hin; cbn [occurrences_args] in Hin; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply (occurrences_expr_ge e parent (PrintlnArgument aidx) me id occ Hin).
  - specialize (IH parent (S aidx) (Pos.succ (end_expr me e)) id occ Hin).
    pose proof (end_expr_ge e me). lia.
Qed.

Lemma occurrences_args_lt : forall es parent aidx me id occ,
  In (id, occ) (occurrences_args parent aidx me es) -> (id < next_exprs me es)%positive.
Proof.
  induction es as [|e rest IH]; intros parent aidx me id occ Hin; cbn [occurrences_args next_exprs] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_expr_le e parent (PrintlnArgument aidx) me id occ Hin) as Hle.
    pose proof (next_exprs_ge rest (Pos.succ (end_expr me e))). lia.
  - apply (IH parent (S aidx) (Pos.succ (end_expr me e)) id occ Hin).
Qed.

Lemma occurrences_stmt_ge : forall s parent sidx me id occ,
  In (id, occ) (occurrences_stmt parent sidx me s) -> (me <= id)%positive.
Proof.
  intros [args] parent sidx me id occ Hin. cbn [occurrences_stmt] in Hin.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|].
  apply (occurrences_args_ge args me 0 (Pos.succ me) id occ) in Hin. lia.
Qed.

Lemma occurrences_stmt_le : forall s parent sidx me id occ,
  In (id, occ) (occurrences_stmt parent sidx me s) -> (id <= end_stmt me s)%positive.
Proof.
  intros [args] parent sidx me id occ Hin. cbn [occurrences_stmt end_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. pose proof (next_exprs_ge args (Pos.succ me)). lia.
  - apply (occurrences_args_lt args me 0 (Pos.succ me) id occ) in Hin. lia.
Qed.

Lemma occurrences_stmts_ge : forall ss parent sidx me id occ,
  In (id, occ) (occurrences_stmts parent sidx me ss) -> (me <= id)%positive.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me id occ Hin; cbn [occurrences_stmts] in Hin; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply (occurrences_stmt_ge s parent sidx me id occ Hin).
  - specialize (IH parent (S sidx) (Pos.succ (end_stmt me s)) id occ Hin).
    pose proof (end_stmt_ge s me). lia.
Qed.

Lemma occurrences_stmts_lt : forall ss parent sidx me id occ,
  In (id, occ) (occurrences_stmts parent sidx me ss) -> (id < next_stmts me ss)%positive.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me id occ Hin; cbn [occurrences_stmts next_stmts] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_stmt_le s parent sidx me id occ Hin) as Hle.
    pose proof (next_stmts_ge rest (Pos.succ (end_stmt me s))). lia.
  - apply (IH parent (S sidx) (Pos.succ (end_stmt me s)) id occ Hin).
Qed.

Lemma occurrences_decl_ge : forall d parent didx me id occ,
  In (id, occ) (occurrences_decl parent didx me d) -> (me <= id)%positive.
Proof.
  intros [body] parent didx me id occ Hin. cbn [occurrences_decl] in Hin.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; lia|].
  apply (occurrences_stmts_ge body me 0 (Pos.succ me) id occ) in Hin. lia.
Qed.

Lemma occurrences_decl_le : forall d parent didx me id occ,
  In (id, occ) (occurrences_decl parent didx me d) -> (id <= end_decl me d)%positive.
Proof.
  intros [body] parent didx me id occ Hin. cbn [occurrences_decl end_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. pose proof (next_stmts_ge body (Pos.succ me)). lia.
  - apply (occurrences_stmts_lt body me 0 (Pos.succ me) id occ) in Hin. lia.
Qed.

Lemma occurrences_decls_ge : forall ds parent didx me id occ,
  In (id, occ) (occurrences_decls parent didx me ds) -> (me <= id)%positive.
Proof.
  induction ds as [|d rest IH]; intros parent didx me id occ Hin; cbn [occurrences_decls] in Hin; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply (occurrences_decl_ge d parent didx me id occ Hin).
  - specialize (IH parent (S didx) (Pos.succ (end_decl me d)) id occ Hin).
    pose proof (end_decl_ge d me). lia.
Qed.

Lemma occurrences_decls_lt : forall ds parent didx me id occ,
  In (id, occ) (occurrences_decls parent didx me ds) -> (id < next_decls me ds)%positive.
Proof.
  induction ds as [|d rest IH]; intros parent didx me id occ Hin; cbn [occurrences_decls next_decls] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_decl_le d parent didx me id occ Hin) as Hle.
    pose proof (next_decls_ge rest (Pos.succ (end_decl me d))). lia.
  - apply (IH parent (S didx) (Pos.succ (end_decl me d)) id occ Hin).
Qed.

(* --- SOUNDNESS: every emitted (id, occ) IS the exact source occurrence [source_occurrence_at] designates. --- *)

Lemma occurrences_expr_sound : forall e parent role me id occ,
  In (id, occ) (occurrences_expr parent role me e) -> occurrence_expr' parent role me e id = Some occ.
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me id occ Hin; cbn [occurrences_expr occurrence_expr'] in *;
    try (destruct Hin as [Heq|[]]; injection Heq as <- <-; rewrite Pos.eqb_refl; reflexivity);
    (destruct Hin as [Heq|Hin];
     [ injection Heq as <- <-; rewrite Pos.eqb_refl; reflexivity |];
     destruct Hin as [Heq|Hin];
     [ injection Heq as <- <-;
       destruct (Pos.eqb_spec (Pos.succ me) me); [lia|]; rewrite Pos.eqb_refl; reflexivity |];
     pose proof (occurrences_expr_ge x me ConversionOperand (Pos.succ (Pos.succ me)) id occ Hin) as Hge;
     destruct (Pos.eqb_spec id me); [lia|];
     destruct (Pos.eqb_spec id (Pos.succ me)); [lia|];
     apply (IHx me ConversionOperand (Pos.succ (Pos.succ me)) id occ Hin)).
Qed.

Lemma occurrences_args_sound : forall es parent aidx me id occ,
  In (id, occ) (occurrences_args parent aidx me es) -> occurrence_exprs' parent aidx me es id = Some occ.
Proof.
  induction es as [|e rest IH]; intros parent aidx me id occ Hin; cbn [occurrences_args occurrence_exprs'] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_expr_le e parent (PrintlnArgument aidx) me id occ Hin) as Hle.
    destruct (Pos.leb_spec id (end_expr me e)); [| lia].
    apply (occurrences_expr_sound e parent (PrintlnArgument aidx) me id occ Hin).
  - pose proof (occurrences_args_ge rest parent (S aidx) (Pos.succ (end_expr me e)) id occ Hin) as Hge.
    destruct (Pos.leb_spec id (end_expr me e)); [lia|].
    apply (IH parent (S aidx) (Pos.succ (end_expr me e)) id occ Hin).
Qed.

Lemma occurrences_stmt_sound : forall s parent sidx me id occ,
  In (id, occ) (occurrences_stmt parent sidx me s) -> occurrence_stmt' parent sidx me s id = Some occ.
Proof.
  intros [args] parent sidx me id occ Hin. cbn [occurrences_stmt occurrence_stmt'] in *.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; rewrite Pos.eqb_refl; reflexivity|].
  pose proof (occurrences_args_ge args me 0 (Pos.succ me) id occ Hin) as Hge.
  destruct (Pos.eqb_spec id me); [lia|].
  apply (occurrences_args_sound args me 0 (Pos.succ me) id occ Hin).
Qed.

Lemma occurrences_stmts_sound : forall ss parent sidx me id occ,
  In (id, occ) (occurrences_stmts parent sidx me ss) -> occurrence_stmts' parent sidx me ss id = Some occ.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me id occ Hin; cbn [occurrences_stmts occurrence_stmts'] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_stmt_le s parent sidx me id occ Hin) as Hle.
    destruct (Pos.leb_spec id (end_stmt me s)); [| lia].
    apply (occurrences_stmt_sound s parent sidx me id occ Hin).
  - pose proof (occurrences_stmts_ge rest parent (S sidx) (Pos.succ (end_stmt me s)) id occ Hin) as Hge.
    destruct (Pos.leb_spec id (end_stmt me s)); [lia|].
    apply (IH parent (S sidx) (Pos.succ (end_stmt me s)) id occ Hin).
Qed.

Lemma occurrences_decl_sound : forall d parent didx me id occ,
  In (id, occ) (occurrences_decl parent didx me d) -> occurrence_decl' parent didx me d id = Some occ.
Proof.
  intros [body] parent didx me id occ Hin. cbn [occurrences_decl occurrence_decl'] in *.
  destruct Hin as [Heq|Hin]; [injection Heq as <- <-; rewrite Pos.eqb_refl; reflexivity|].
  pose proof (occurrences_stmts_ge body me 0 (Pos.succ me) id occ Hin) as Hge.
  destruct (Pos.eqb_spec id me); [lia|].
  apply (occurrences_stmts_sound body me 0 (Pos.succ me) id occ Hin).
Qed.

Lemma occurrences_decls_sound : forall ds parent didx me id occ,
  In (id, occ) (occurrences_decls parent didx me ds) -> occurrence_decls' parent didx me ds id = Some occ.
Proof.
  induction ds as [|d rest IH]; intros parent didx me id occ Hin; cbn [occurrences_decls occurrence_decls'] in *; [destruct Hin|].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - pose proof (occurrences_decl_le d parent didx me id occ Hin) as Hle.
    destruct (Pos.leb_spec id (end_decl me d)); [| lia].
    apply (occurrences_decl_sound d parent didx me id occ Hin).
  - pose proof (occurrences_decls_ge rest parent (S didx) (Pos.succ (end_decl me d)) id occ Hin) as Hge.
    destruct (Pos.leb_spec id (end_decl me d)); [lia|].
    apply (IH parent (S didx) (Pos.succ (end_decl me d)) id occ Hin).
Qed.

(* the whole-file traversal is EXACT: every emitted (id, occ) is the source occurrence [source_occurrence_at]
   designates at [id] — the fragment carried by the ONE structural pass matches the independent spec. *)
Theorem occurrences_file_sound : forall f id occ,
  In (id, occ) (occurrences_file f) -> source_occurrence_at f id = Some occ.
Proof.
  intros f id occ. unfold occurrences_file, source_occurrence_at.
  destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  intros [Heq | [Heq | Hin]].
  - injection Heq as <- <-. rewrite Pos.eqb_refl. reflexivity.
  - injection Heq as <- <-. rewrite (proj2 (Pos.eqb_neq package_id root_id) ltac:(unfold package_id, root_id; discriminate)).
    rewrite Pos.eqb_refl. reflexivity.
  - pose proof (occurrences_decls_ge (Syntax.declarations f) root_id 0 (Pos.succ package_id) id occ Hin) as Hge.
    rewrite (proj2 (Pos.eqb_neq id root_id) ltac:(unfold package_id, root_id in *; lia)).
    rewrite (proj2 (Pos.eqb_neq id package_id) ltac:(unfold package_id in *; lia)).
    apply (occurrences_decls_sound (Syntax.declarations f) root_id 0 (Pos.succ package_id) id occ Hin).
Qed.

(* --- COMPLETENESS: every source occurrence the spec designates is emitted by the traversal. --- *)

Lemma occurrences_expr_complete : forall e parent role me id occ,
  occurrence_expr' parent role me e id = Some occ -> In (id, occ) (occurrences_expr parent role me e).
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me id occ H; cbn [occurrences_expr occurrence_expr'] in *;
    try (destruct (Pos.eqb_spec id me); [injection H as <-; subst id; left; reflexivity | discriminate]);
    (destruct (Pos.eqb_spec id me);
     [ injection H as <-; subst id; left; reflexivity |];
     destruct (Pos.eqb_spec id (Pos.succ me));
     [ injection H as <-; subst id; right; left; reflexivity |];
     right; right; apply (IHx me ConversionOperand (Pos.succ (Pos.succ me)) id occ H)).
Qed.

Lemma occurrences_args_complete : forall es parent aidx me id occ,
  occurrence_exprs' parent aidx me es id = Some occ -> In (id, occ) (occurrences_args parent aidx me es).
Proof.
  induction es as [|e rest IH]; intros parent aidx me id occ H; cbn [occurrences_args occurrence_exprs'] in *; [discriminate|].
  destruct (Pos.leb_spec id (end_expr me e)).
  - apply in_or_app. left. apply (occurrences_expr_complete e parent (PrintlnArgument aidx) me id occ H).
  - apply in_or_app. right. apply (IH parent (S aidx) (Pos.succ (end_expr me e)) id occ H).
Qed.

Lemma occurrences_stmt_complete : forall s parent sidx me id occ,
  occurrence_stmt' parent sidx me s id = Some occ -> In (id, occ) (occurrences_stmt parent sidx me s).
Proof.
  intros [args] parent sidx me id occ H. cbn [occurrences_stmt occurrence_stmt'] in *.
  destruct (Pos.eqb_spec id me).
  - injection H as <-. subst id. left. reflexivity.
  - right. apply (occurrences_args_complete args me 0 (Pos.succ me) id occ H).
Qed.

Lemma occurrences_stmts_complete : forall ss parent sidx me id occ,
  occurrence_stmts' parent sidx me ss id = Some occ -> In (id, occ) (occurrences_stmts parent sidx me ss).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me id occ H; cbn [occurrences_stmts occurrence_stmts'] in *; [discriminate|].
  destruct (Pos.leb_spec id (end_stmt me s)).
  - apply in_or_app. left. apply (occurrences_stmt_complete s parent sidx me id occ H).
  - apply in_or_app. right. apply (IH parent (S sidx) (Pos.succ (end_stmt me s)) id occ H).
Qed.

Lemma occurrences_decl_complete : forall d parent didx me id occ,
  occurrence_decl' parent didx me d id = Some occ -> In (id, occ) (occurrences_decl parent didx me d).
Proof.
  intros [body] parent didx me id occ H. cbn [occurrences_decl occurrence_decl'] in *.
  destruct (Pos.eqb_spec id me).
  - injection H as <-. subst id. left. reflexivity.
  - right. apply (occurrences_stmts_complete body me 0 (Pos.succ me) id occ H).
Qed.

Lemma occurrences_decls_complete : forall ds parent didx me id occ,
  occurrence_decls' parent didx me ds id = Some occ -> In (id, occ) (occurrences_decls parent didx me ds).
Proof.
  induction ds as [|d rest IH]; intros parent didx me id occ H; cbn [occurrences_decls occurrence_decls'] in *; [discriminate|].
  destruct (Pos.leb_spec id (end_decl me d)).
  - apply in_or_app. left. apply (occurrences_decl_complete d parent didx me id occ H).
  - apply in_or_app. right. apply (IH parent (S didx) (Pos.succ (end_decl me d)) id occ H).
Qed.

Theorem occurrences_file_complete : forall f id occ,
  source_occurrence_at f id = Some occ -> In (id, occ) (occurrences_file f).
Proof.
  intros f id occ. unfold occurrences_file, source_occurrence_at.
  destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  destruct (Pos.eqb_spec id root_id).
  - intros Heq. injection Heq as <-. subst id. left. reflexivity.
  - destruct (Pos.eqb_spec id package_id).
    + intros Heq. injection Heq as <-. subst id. right; left. reflexivity.
    + intros H. right; right. apply (occurrences_decls_complete (Syntax.declarations f) root_id 0 (Pos.succ package_id) id occ H).
Qed.

(* the traversal is EXACT: it lists exactly the graph of [source_occurrence_at] over the valid ids. *)
Theorem occurrences_file_exact : forall f id occ,
  In (id, occ) (occurrences_file f) <-> source_occurrence_at f id = Some occ.
Proof. intros f id occ. split; [apply occurrences_file_sound | apply occurrences_file_complete]. Qed.

(* --- CANONICAL PREORDER ORDER: the emitted ids are strictly increasing. --- *)

Lemma strongly_sorted_append_positive : forall (l1 l2 : list positive),
  StronglySorted Pos.lt l1 -> StronglySorted Pos.lt l2 ->
  (forall x y, In x l1 -> In y l2 -> (x < y)%positive) ->
  StronglySorted Pos.lt (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 H1 H2 Hcross; cbn [app]; [exact H2|].
  inversion H1 as [|a0 l0 HSS1 HF1]; subst.
  constructor.
  - apply IH; [exact HSS1 | exact H2 | intros x y Hx Hy; apply Hcross; [right; exact Hx | exact Hy]].
  - apply Forall_forall. intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|Hy].
    + rewrite Forall_forall in HF1. apply HF1; exact Hy.
    + apply Hcross; [left; reflexivity | exact Hy].
Qed.

Lemma occurrences_expr_fst : forall e parent role me y,
  In y (map fst (occurrences_expr parent role me e)) -> (me <= y)%positive /\ (y <= end_expr me e)%positive.
Proof.
  intros e parent role me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_expr_ge e parent role me id occ Hin) | apply (occurrences_expr_le e parent role me id occ Hin) ].
Qed.
Lemma occurrences_args_fst : forall es parent aidx me y,
  In y (map fst (occurrences_args parent aidx me es)) -> (me <= y)%positive /\ (y < next_exprs me es)%positive.
Proof.
  intros es parent aidx me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_args_ge es parent aidx me id occ Hin) | apply (occurrences_args_lt es parent aidx me id occ Hin) ].
Qed.
Lemma occurrences_stmt_fst : forall s parent sidx me y,
  In y (map fst (occurrences_stmt parent sidx me s)) -> (me <= y)%positive /\ (y <= end_stmt me s)%positive.
Proof.
  intros s parent sidx me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_stmt_ge s parent sidx me id occ Hin) | apply (occurrences_stmt_le s parent sidx me id occ Hin) ].
Qed.
Lemma occurrences_stmts_fst : forall ss parent sidx me y,
  In y (map fst (occurrences_stmts parent sidx me ss)) -> (me <= y)%positive /\ (y < next_stmts me ss)%positive.
Proof.
  intros ss parent sidx me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_stmts_ge ss parent sidx me id occ Hin) | apply (occurrences_stmts_lt ss parent sidx me id occ Hin) ].
Qed.
Lemma occurrences_decl_fst : forall d parent didx me y,
  In y (map fst (occurrences_decl parent didx me d)) -> (me <= y)%positive /\ (y <= end_decl me d)%positive.
Proof.
  intros d parent didx me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_decl_ge d parent didx me id occ Hin) | apply (occurrences_decl_le d parent didx me id occ Hin) ].
Qed.
Lemma occurrences_decls_fst : forall ds parent didx me y,
  In y (map fst (occurrences_decls parent didx me ds)) -> (me <= y)%positive /\ (y < next_decls me ds)%positive.
Proof.
  intros ds parent didx me y H. apply in_map_iff in H. destruct H as [[id occ] [Hf Hin]]. cbn in Hf. subst y.
  split; [ apply (occurrences_decls_ge ds parent didx me id occ Hin) | apply (occurrences_decls_lt ds parent didx me id occ Hin) ].
Qed.

Lemma occurrences_expr_sorted : forall e parent role me, StronglySorted Pos.lt (map fst (occurrences_expr parent role me e)).
Proof.
  induction e as [ b | n1 | n2 | s | df | dcx | ts x IHx ];
    intros parent role me; cbn [occurrences_expr map fst];
    try (solve [ repeat constructor ]).
  constructor.
  - constructor.
    + apply IHx.
    + apply Forall_forall; intros y Hy;
      pose proof (occurrences_expr_fst x me ConversionOperand (Pos.succ (Pos.succ me)) y Hy) as [Hge _]; lia.
  - apply Forall_forall; intros y Hy; cbn [In] in Hy; destruct Hy as [Hy|Hy];
    [ subst y; lia
    | pose proof (occurrences_expr_fst x me ConversionOperand (Pos.succ (Pos.succ me)) y Hy) as [Hge _]; lia ].
Qed.

Lemma occurrences_args_sorted : forall es parent aidx me, StronglySorted Pos.lt (map fst (occurrences_args parent aidx me es)).
Proof.
  induction es as [|e rest IH]; intros parent aidx me; cbn [occurrences_args]; [constructor|].
  rewrite map_app. apply strongly_sorted_append_positive.
  - unfold occurrences_arg. apply occurrences_expr_sorted.
  - apply IH.
  - intros x y Hx Hy. pose proof (occurrences_expr_fst e parent (PrintlnArgument aidx) me x Hx) as [_ Hxle].
    pose proof (occurrences_args_fst rest parent (S aidx) (Pos.succ (end_expr me e)) y Hy) as [Hyge _]. lia.
Qed.

Lemma occurrences_stmt_sorted : forall s parent sidx me, StronglySorted Pos.lt (map fst (occurrences_stmt parent sidx me s)).
Proof.
  intros [args] parent sidx me. cbn [occurrences_stmt map fst].
  constructor.
  - apply occurrences_args_sorted.
  - apply Forall_forall. intros y Hy.
    pose proof (occurrences_args_fst args me 0 (Pos.succ me) y Hy) as [Hge _]. lia.
Qed.

Lemma occurrences_stmts_sorted : forall ss parent sidx me, StronglySorted Pos.lt (map fst (occurrences_stmts parent sidx me ss)).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; cbn [occurrences_stmts]; [constructor|].
  rewrite map_app. apply strongly_sorted_append_positive.
  - apply occurrences_stmt_sorted.
  - apply IH.
  - intros x y Hx Hy. pose proof (occurrences_stmt_fst s parent sidx me x Hx) as [_ Hxle].
    pose proof (occurrences_stmts_fst rest parent (S sidx) (Pos.succ (end_stmt me s)) y Hy) as [Hyge _]. lia.
Qed.

Lemma occurrences_decl_sorted : forall d parent didx me, StronglySorted Pos.lt (map fst (occurrences_decl parent didx me d)).
Proof.
  intros [body] parent didx me. cbn [occurrences_decl map fst].
  constructor.
  - apply occurrences_stmts_sorted.
  - apply Forall_forall. intros y Hy.
    pose proof (occurrences_stmts_fst body me 0 (Pos.succ me) y Hy) as [Hge _]. lia.
Qed.

Lemma occurrences_decls_sorted : forall ds parent didx me, StronglySorted Pos.lt (map fst (occurrences_decls parent didx me ds)).
Proof.
  induction ds as [|d rest IH]; intros parent didx me; cbn [occurrences_decls]; [constructor|].
  rewrite map_app. apply strongly_sorted_append_positive.
  - apply occurrences_decl_sorted.
  - apply IH.
  - intros x y Hx Hy. pose proof (occurrences_decl_fst d parent didx me x Hx) as [_ Hxle].
    pose proof (occurrences_decls_fst rest parent (S didx) (Pos.succ (end_decl me d)) y Hy) as [Hyge _]. lia.
Qed.

Theorem occurrences_file_sorted : forall f, StronglySorted Pos.lt (map fst (occurrences_file f)).
Proof.
  intros f. unfold occurrences_file. destruct (Syntax.imports f) as [|i ?]; [| destruct i].
  cbn [map fst]. constructor.
  - constructor.
    + apply occurrences_decls_sorted.
    + apply Forall_forall. intros y Hy.
      pose proof (occurrences_decls_fst (Syntax.declarations f) root_id 0 (Pos.succ package_id) y Hy) as [Hge _].
      unfold package_id in *. lia.
  - apply Forall_forall. intros y Hy. cbn [In] in Hy. destruct Hy as [Hy|Hy].
    + subst y. unfold package_id, root_id. lia.
    + pose proof (occurrences_decls_fst (Syntax.declarations f) root_id 0 (Pos.succ package_id) y Hy) as [Hge _].
      unfold package_id, root_id in *. lia.
Qed.

(* NoDup of the emitted ids follows from strict sortedness. *)
Lemma strongly_sorted_no_duplicates : forall (l : list positive), StronglySorted Pos.lt l -> NoDup l.
Proof.
  induction l as [|x rest IH]; intros HS; [constructor|].
  inversion HS as [|a0 l0 HSS HF]; subst. constructor.
  - intros Hin. rewrite Forall_forall in HF. specialize (HF x Hin). lia.
  - apply IH. exact HSS.
Qed.
Theorem occurrences_file_nodup : forall f, NoDup (map fst (occurrences_file f)).
Proof. intros f. apply strongly_sorted_no_duplicates, occurrences_file_sorted. Qed.

(* SINGLE-PASS TRAVERSAL — the honest hot-path implementation of the occurrence stream.

   [occs_*] above is the readable denotational SPECIFICATION of the stream: its per-node [end_expr]/[end_stmt]/
   [end_decl]/[next_*] boundary calls RESCAN each subtree, so evaluating it would be QUADRATIC on nested
   conversions / long sibling runs.  The [walk_*] family computes the SAME stream in ONE structural pass — each
   function RETURNS the next-free local id, so a parent reads its child's subtree end from the returned cursor
   ([Pos.pred] of it) and a sibling starts at it, with NO boundary rescan.  [walk_file_eq] proves
   [walk_file f = occurrences_file f], so every exactness / order / NoDup theorem proved for the spec transfers to the
   pass, and [visit_file] runs the single-pass [walk_file] (one traversal per file, one occurrence each). *)

Fixpoint walk_expr (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr)
  : list (positive * Occurrence) * positive :=
  match e with
  | Syntax.BoolLiteral _ | Syntax.IntegerLiteral _ | Syntax.NegatedIntegerLiteral _ | Syntax.StringLiteral _ | Syntax.FloatLiteral _ | Syntax.ComplexLiteral _ =>
      ([(me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role me)], Pos.succ me)
  | Syntax.Convert ts x =>
      let tn := Pos.succ me in
      let '(sub, nxt) := walk_expr me ConversionOperand (Pos.succ tn) x in
      ((me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (Pos.pred nxt))
         :: (tn, MakeOccurrence TypeNameKind (TypeNameView ts) (Some me) ConversionTarget tn)
         :: sub, nxt)
  end.

Lemma walk_expr_snd : forall e parent role me, snd (walk_expr parent role me e) = Pos.succ (end_expr me e).
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent role me; try reflexivity;
    cbn [walk_expr end_expr]; specialize (IHx me ConversionOperand (Pos.succ (Pos.succ me)));
    destruct (walk_expr me ConversionOperand (Pos.succ (Pos.succ me)) x) as [sub nxt]; cbn [snd] in *; exact IHx.
Qed.

Lemma walk_expr_eq : forall e parent role me, fst (walk_expr parent role me e) = occurrences_expr parent role me e.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent role me; try reflexivity;
    cbn [walk_expr occurrences_expr end_expr];
    pose proof (walk_expr_snd x me ConversionOperand (Pos.succ (Pos.succ me))) as Hs;
    specialize (IHx me ConversionOperand (Pos.succ (Pos.succ me)));
    destruct (walk_expr me ConversionOperand (Pos.succ (Pos.succ me)) x) as [sub nxt]; cbn [fst snd] in Hs, IHx |- *;
    subst nxt; rewrite Pos.pred_succ, IHx; reflexivity.
Qed.

Fixpoint walk_args (parent : positive) (aidx : nat) (me : positive) (es : list Syntax.Expr)
  : list (positive * Occurrence) * positive :=
  match es with
  | [] => ([], me)
  | e :: rest =>
      let '(h, nxt) := walk_expr parent (PrintlnArgument aidx) me e in
      let '(t, nxt2) := walk_args parent (S aidx) nxt rest in
      (h ++ t, nxt2)
  end.

Lemma walk_args_snd : forall es parent aidx me, snd (walk_args parent aidx me es) = next_exprs me es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [walk_args next_exprs].
  pose proof (walk_expr_snd e parent (PrintlnArgument aidx) me) as He.
  destruct (walk_expr parent (PrintlnArgument aidx) me e) as [h nxt]; cbn [snd] in He.
  specialize (IH parent (S aidx) nxt).
  destruct (walk_args parent (S aidx) nxt rest) as [t nxt2]; cbn [snd] in *.
  rewrite IH, He. reflexivity.
Qed.

Lemma walk_args_eq : forall es parent aidx me, fst (walk_args parent aidx me es) = occurrences_args parent aidx me es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [walk_args occurrences_args occurrences_arg].
  pose proof (walk_expr_snd e parent (PrintlnArgument aidx) me) as He.
  pose proof (walk_expr_eq e parent (PrintlnArgument aidx) me) as Hee.
  destruct (walk_expr parent (PrintlnArgument aidx) me e) as [h nxt]; cbn [fst snd] in He, Hee.
  specialize (IH parent (S aidx) nxt).
  destruct (walk_args parent (S aidx) nxt rest) as [t nxt2]; cbn [fst] in IH |- *.
  subst nxt. rewrite Hee, IH. reflexivity.
Qed.

Definition walk_stmt (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt)
  : list (positive * Occurrence) * positive :=
  match s with
  | Syntax.Println args =>
      let '(a, nxt) := walk_args me 0 (Pos.succ me) args in
      ((me, MakeOccurrence StatementKind (StatementView s) (Some parent) (DeclarationStatement sidx) (Pos.pred nxt)) :: a, nxt)
  end.

Lemma walk_stmt_snd : forall s parent sidx me, snd (walk_stmt parent sidx me s) = Pos.succ (end_stmt me s).
Proof.
  intros [args] parent sidx me. cbn [walk_stmt end_stmt].
  pose proof (walk_args_snd args me 0 (Pos.succ me)) as Ha.
  destruct (walk_args me 0 (Pos.succ me) args) as [a nxt]; cbn [snd] in *.
  rewrite Ha, Pos.succ_pred; [ reflexivity | pose proof (next_exprs_ge args (Pos.succ me)); lia ].
Qed.

Lemma walk_stmt_eq : forall s parent sidx me, fst (walk_stmt parent sidx me s) = occurrences_stmt parent sidx me s.
Proof.
  intros [args] parent sidx me. cbn [walk_stmt occurrences_stmt end_stmt].
  pose proof (walk_args_snd args me 0 (Pos.succ me)) as Hs.
  pose proof (walk_args_eq args me 0 (Pos.succ me)) as Ha.
  destruct (walk_args me 0 (Pos.succ me) args) as [a nxt]; cbn [fst snd] in Hs, Ha |- *.
  subst nxt. rewrite Ha. reflexivity.
Qed.

Fixpoint walk_stmts (parent : positive) (sidx : nat) (me : positive) (ss : list Syntax.Stmt)
  : list (positive * Occurrence) * positive :=
  match ss with
  | [] => ([], me)
  | s :: rest =>
      let '(h, nxt) := walk_stmt parent sidx me s in
      let '(t, nxt2) := walk_stmts parent (S sidx) nxt rest in
      (h ++ t, nxt2)
  end.

Lemma walk_stmts_snd : forall ss parent sidx me, snd (walk_stmts parent sidx me ss) = next_stmts me ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [walk_stmts next_stmts].
  pose proof (walk_stmt_snd s parent sidx me) as Hs.
  destruct (walk_stmt parent sidx me s) as [h nxt]; cbn [snd] in Hs.
  specialize (IH parent (S sidx) nxt).
  destruct (walk_stmts parent (S sidx) nxt rest) as [t nxt2]; cbn [snd] in *.
  rewrite IH, Hs. reflexivity.
Qed.

Lemma walk_stmts_eq : forall ss parent sidx me, fst (walk_stmts parent sidx me ss) = occurrences_stmts parent sidx me ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [walk_stmts occurrences_stmts].
  pose proof (walk_stmt_snd s parent sidx me) as Hs.
  pose proof (walk_stmt_eq s parent sidx me) as Hse.
  destruct (walk_stmt parent sidx me s) as [h nxt]; cbn [fst snd] in Hs, Hse.
  specialize (IH parent (S sidx) nxt).
  destruct (walk_stmts parent (S sidx) nxt rest) as [t nxt2]; cbn [fst] in IH |- *.
  subst nxt. rewrite Hse, IH. reflexivity.
Qed.

Definition walk_decl (parent : positive) (didx : nat) (me : positive) (d : Syntax.Decl)
  : list (positive * Occurrence) * positive :=
  match d with
  | Syntax.Main body =>
      let '(b, nxt) := walk_stmts me 0 (Pos.succ me) body in
      ((me, MakeOccurrence DeclarationKind (DeclarationView d) (Some parent) (FileDeclaration didx) (Pos.pred nxt)) :: b, nxt)
  end.

Lemma walk_decl_snd : forall d parent didx me, snd (walk_decl parent didx me d) = Pos.succ (end_decl me d).
Proof.
  intros [body] parent didx me. cbn [walk_decl end_decl].
  pose proof (walk_stmts_snd body me 0 (Pos.succ me)) as Hb.
  destruct (walk_stmts me 0 (Pos.succ me) body) as [b nxt]; cbn [snd] in *.
  rewrite Hb, Pos.succ_pred; [ reflexivity | pose proof (next_stmts_ge body (Pos.succ me)); lia ].
Qed.

Lemma walk_decl_eq : forall d parent didx me, fst (walk_decl parent didx me d) = occurrences_decl parent didx me d.
Proof.
  intros [body] parent didx me. cbn [walk_decl occurrences_decl end_decl].
  pose proof (walk_stmts_snd body me 0 (Pos.succ me)) as Hs.
  pose proof (walk_stmts_eq body me 0 (Pos.succ me)) as Hb.
  destruct (walk_stmts me 0 (Pos.succ me) body) as [b nxt]; cbn [fst snd] in Hs, Hb |- *.
  subst nxt. rewrite Hb. reflexivity.
Qed.

Fixpoint walk_decls (parent : positive) (didx : nat) (me : positive) (ds : list Syntax.Decl)
  : list (positive * Occurrence) * positive :=
  match ds with
  | [] => ([], me)
  | d :: rest =>
      let '(h, nxt) := walk_decl parent didx me d in
      let '(t, nxt2) := walk_decls parent (S didx) nxt rest in
      (h ++ t, nxt2)
  end.

Lemma walk_decls_snd : forall ds parent didx me, snd (walk_decls parent didx me ds) = next_decls me ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [walk_decls next_decls].
  pose proof (walk_decl_snd d parent didx me) as Hs.
  destruct (walk_decl parent didx me d) as [h nxt]; cbn [snd] in Hs.
  specialize (IH parent (S didx) nxt).
  destruct (walk_decls parent (S didx) nxt rest) as [t nxt2]; cbn [snd] in *.
  rewrite IH, Hs. reflexivity.
Qed.

Lemma walk_decls_eq : forall ds parent didx me, fst (walk_decls parent didx me ds) = occurrences_decls parent didx me ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [walk_decls occurrences_decls].
  pose proof (walk_decl_snd d parent didx me) as Hs.
  pose proof (walk_decl_eq d parent didx me) as Hde.
  destruct (walk_decl parent didx me d) as [h nxt]; cbn [fst snd] in Hs, Hde.
  specialize (IH parent (S didx) nxt).
  destruct (walk_decls parent (S didx) nxt rest) as [t nxt2]; cbn [fst] in IH |- *.
  subst nxt. rewrite Hde, IH. reflexivity.
Qed.

Definition walk_file (f : Syntax.File) : list (positive * Occurrence) :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      let '(ds, nxt) := walk_decls root_id 0 (Pos.succ package_id) (Syntax.declarations f) in
      (root_id, MakeOccurrence FileKind (FileView f) None FileRoot (Pos.pred nxt))
        :: (package_id, MakeOccurrence PackageClauseKind (PackageClauseView (Syntax.package f)) (Some root_id) FilePackage package_id)
        :: ds
  end.

Lemma walk_file_eq : forall f, walk_file f = occurrences_file f.
Proof.
  intros f. unfold walk_file, occurrences_file. destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  pose proof (walk_decls_snd (Syntax.declarations f) root_id 0 (Pos.succ package_id)) as Hs.
  pose proof (walk_decls_eq (Syntax.declarations f) root_id 0 (Pos.succ package_id)) as Hd.
  destruct (walk_decls root_id 0 (Pos.succ package_id) (Syntax.declarations f)) as [ds nxt]; cbn [fst snd] in Hs, Hd.
  subst nxt. rewrite Hd. reflexivity.
Qed.

(* The public interface of the reference layer.  It exposes the abstract PROGRAM-indexed types, the validated
   MINTING boundaries, the projections, the TOTAL navigation API, and the theorem surfaces — but NOT the raw
   record constructors nor the raw index map.  Sealing the module against this signature makes "the only way
   to mint a reference is a validated function" TRUE rather than aspirational.  Every reference is indexed by
   the EXACT [Syntax.Program] snapshot. *)
Module Type SNAPSHOT_SIG.
  Parameter FileRef     : Syntax.Program -> Type.
  Parameter NodeRef     : Syntax.Program -> Type.
  Parameter Syntax : Syntax.Program -> Type.
  Parameter index_program : forall p, Syntax p.
  Parameter file_of_path : forall p, FilePath.T -> option (FileRef p).
  Parameter ref_of_key   : forall p, Syntax p -> Key -> option (NodeRef p).
  Parameter file_ref_source : forall {p}, FileRef p -> Syntax.File.
  Parameter file_ref_path : forall {p}, FileRef p -> FilePath.T.
  Parameter node_ref_file  : forall {p}, NodeRef p -> FileRef p.
  Parameter node_ref_local : forall {p}, NodeRef p -> positive.
  Parameter node_ref_valid : forall {p} (r : NodeRef p),
    valid_localb (file_ref_source (node_ref_file r)) (node_ref_local r) = true.
  Parameter node_ref_key   : forall {p}, NodeRef p -> Key.
  Parameter node_ref_key_eq : forall {p} (r : NodeRef p),
    node_ref_key r = MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
  Parameter ref_meta         : forall {p}, Syntax p -> NodeRef p -> Meta.
  Parameter node_kind        : forall {p}, Syntax p -> NodeRef p -> Kind.
  Parameter node_role        : forall {p}, Syntax p -> NodeRef p -> Role.
  Parameter node_subtree_end : forall {p}, Syntax p -> NodeRef p -> positive.
  Parameter containing_file  : forall {p}, NodeRef p -> FileRef p.
  Parameter parent_of        : forall {p}, Syntax p -> NodeRef p -> option (NodeRef p).
  Parameter children_of      : forall {p}, Syntax p -> NodeRef p -> list (NodeRef p).
  Parameter node_at          : forall {p}, NodeRef p -> option Syntax.Expr.
  Parameter source_occurrence_of_ref : forall {p}, NodeRef p -> Occurrence.
  Parameter is_ancestor_ref  : forall {p}, Syntax p -> NodeRef p -> NodeRef p -> bool.
  (* identity + total-API correctness *)
  Parameter node_ref_ext : forall p (r1 r2 : NodeRef p),
    node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
  Parameter node_kind_spec : forall p (idx : Syntax p) (r : NodeRef p),
    node_kind idx r = kind (ref_meta idx r).
  Parameter node_role_spec : forall p (idx : Syntax p) (r : NodeRef p),
    node_role idx r = role (ref_meta idx r).
  Parameter ref_meta_built : forall p (idx : Syntax p) (r : NodeRef p),
    Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
  Parameter containing_file_spec : forall p (r : NodeRef p),
    containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = key_path (node_ref_key r).
  Parameter node_ref_key_inj : forall p (r1 r2 : NodeRef p),
    node_ref_key r1 = node_ref_key r2 -> r1 = r2.
  Parameter file_ref_path_inj : forall p (fr1 fr2 : FileRef p),
    file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
  (* navigation *)
  Parameter parent_root : forall p (idx : Syntax p) (r : NodeRef p),
    node_ref_local r = root_id -> parent_of idx r = None.
  Parameter parent_nonroot : forall p (idx : Syntax p) (r : NodeRef p),
    node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
  Parameter parent_same_file : forall p (idx : Syntax p) (r pr : NodeRef p),
    parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
  Parameter children_same_file : forall p (idx : Syntax p) (r cr : NodeRef p),
    In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
  Parameter child_parent : forall p (idx : Syntax p) (r cr : NodeRef p),
    In cr (children_of idx r) -> parent_of idx cr = Some r.
  Parameter parent_child : forall p (idx : Syntax p) (r pr : NodeRef p),
    parent_of idx r = Some pr -> In r (children_of idx pr).
  Parameter children_of_source_order : forall p (idx : Syntax p) (r : NodeRef p),
    StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
  Parameter children_of_nodup : forall p (idx : Syntax p) (r : NodeRef p),
    NoDup (children_of idx r).
  (* minting boundaries: sound + complete, non-circular source membership *)
  Parameter ref_of_key_sound : forall p (idx : Syntax p) (k : Key) (r : NodeRef p),
    ref_of_key p idx k = Some r -> node_ref_key r = k.
  Parameter ref_of_key_complete : forall p (idx : Syntax p) (r : NodeRef p),
    ref_of_key p idx (node_ref_key r) = Some r.
  Parameter file_of_path_complete : forall p (fr : FileRef p),
    file_of_path p (file_ref_path fr) = Some fr.
  Parameter file_of_path_source : forall p (path : FilePath.T) (f : Syntax.File),
    find_file path (Syntax.files p) = Some f ->
    exists fr, file_of_path p path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
  Parameter ref_of_key_source : forall p (idx : Syntax p) (path : FilePath.T) (f : Syntax.File) (local : positive),
    find_file path (Syntax.files p) = Some f -> valid_localb f local = true ->
    exists r, ref_of_key p idx (MakeKey path local) = Some r
              /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
  (* ref-level ancestry: the O(1) interval test, sound + complete vs the parent_of closure. *)
  Inductive RefAncestor (p : Syntax.Program) (idx : Syntax p) : NodeRef p -> NodeRef p -> Prop :=
  | RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor p idx a d
  | RAnc_step : forall a q d, RefAncestor p idx a q -> parent_of idx d = Some q -> RefAncestor p idx a d.
  Parameter ref_ancestry : forall p (idx : Syntax p) (a d : NodeRef p),
    is_ancestor_ref idx a d = true <-> RefAncestor p idx a d.
  (* EXACT source-occurrence correspondence lifted through the sealed API: a valid reference's metadata IS
     its exact source occurrence's metadata (kind/role/parent/subtree), the reference's occurrence IS the
     independent spec's occurrence (pinning the VIEW), node_at agrees with the source view, and parent_of
     returns the EXACT source parent. *)
  Parameter ref_meta_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
  Parameter node_kind_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
  Parameter node_role_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    node_role idx r = occurrence_role (source_occurrence_of_ref r).
  Parameter node_parent_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
  Parameter node_subtree_end_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
  Parameter source_occ_of_ref_eq : forall {p} (r : NodeRef p),
    source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) = Some (source_occurrence_of_ref r).
  Parameter node_at_matches_source_view : forall {p} (r : NodeRef p),
    node_at r = view_expr (source_occurrence_of_ref r).
  Parameter node_parent_ref_matches_source : forall p (idx : Syntax p) (r : NodeRef p),
    match occurrence_parent (source_occurrence_of_ref r) with
    | None     => parent_of idx r = None
    | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
    end.
  (* minting soundness for FileRef + the rejection cases (invalid path / invalid local id). *)
  Parameter file_of_path_sound : forall p (fp : FilePath.T) (fr : FileRef p),
    file_of_path p fp = Some fr -> file_ref_path fr = fp.
  Parameter file_of_path_source_exact : forall p (fp : FilePath.T) (fr : FileRef p),
    file_of_path p fp = Some fr -> find_file fp (Syntax.files p) = Some (file_ref_source fr).
  Parameter ref_of_key_invalid_path : forall p (idx : Syntax p) (fp : FilePath.T) (local : positive),
    find_file fp (Syntax.files p) = None -> ref_of_key p idx (MakeKey fp local) = None.
  Parameter ref_of_key_invalid_local : forall p (idx : Syntax p) (fp : FilePath.T) (f : Syntax.File) (local : positive),
    find_file fp (Syntax.files p) = Some f -> valid_localb f local = false -> ref_of_key p idx (MakeKey fp local) = None.
  (* decidable NodeRef equality (reference identity IS Key identity). *)
  Parameter noderef_eq_dec : forall {p} (r1 r2 : NodeRef p), {r1 = r2} + {r1 <> r2}.
  (* the file-root reference + the CANONICAL preorder enumeration of ALL a file's references, and reachability
     of every occurrence from the file root by repeated parent links. *)
  Parameter file_root_ref : forall {p}, FileRef p -> NodeRef p.
  Parameter file_root_ref_local : forall p (fr : FileRef p), node_ref_local (file_root_ref fr) = root_id.
  Parameter file_root_ref_file : forall p (fr : FileRef p), node_ref_file (file_root_ref fr) = fr.
  (* the canonical reference enumeration REUSES the passed Syntax (one outer-map lookup for the file's
     precomputed File) — it does NOT rebuild the per-file index. *)
  Parameter file_refs : forall {p}, Syntax p -> FileRef p -> list (NodeRef p).
  Parameter file_refs_same_file : forall p (idx : Syntax p) (fr : FileRef p) (r : NodeRef p),
    In r (file_refs idx fr) -> node_ref_file r = fr.
  Parameter file_refs_complete : forall p (idx : Syntax p) (fr : FileRef p) (r : NodeRef p),
    node_ref_file r = fr -> In r (file_refs idx fr).
  Parameter file_refs_nodup : forall p (idx : Syntax p) (fr : FileRef p), NoDup (file_refs idx fr).
  Parameter file_refs_source_order : forall p (idx : Syntax p) (fr : FileRef p),
    StronglySorted Pos.lt (map node_ref_local (file_refs idx fr)).
  Parameter file_root_ref_in_refs : forall p (idx : Syntax p) (fr : FileRef p),
    In (file_root_ref fr) (file_refs idx fr).
  (* reachability: every occurrence reaches the file root by repeated parent links (the root is a strict
     ancestor of every non-root occurrence), and every enumerated reference is the root or reachable from it. *)
  Parameter reachable_from_root : forall p (idx : Syntax p) (r : NodeRef p),
    node_ref_local r <> root_id -> RefAncestor p idx (file_root_ref (node_ref_file r)) r.
  Parameter refs_reachable : forall p (idx : Syntax p) (fr : FileRef p) (r : NodeRef p),
    In r (file_refs idx fr) -> r = file_root_ref fr \/ RefAncestor p idx (file_root_ref fr) r.
  (* the canonical INDEXED TRAVERSAL: ONE structural pass over the file's source yields each occurrence's
     validated NodeRef paired with its ORIGINAL syntax (its Occurrence, which carries the syntax VIEW) —
     the fragment comes from the pass, never a per-node search.  It is EXACT (the paired occurrence IS the
     reference's [source_occurrence_of_ref]) and same-file, COMPLETE over the file, in canonical source
     preorder ORDER, and NoDup. *)
  Parameter visit_file : forall {p}, FileRef p -> list (NodeRef p * Occurrence).
  Parameter visit_file_view : forall p (fr : FileRef p) (r : NodeRef p) (occ : Occurrence),
    In (r, occ) (visit_file fr) -> occ = source_occurrence_of_ref r /\ node_ref_file r = fr.
  Parameter visit_file_complete : forall p (fr : FileRef p) (r : NodeRef p),
    node_ref_file r = fr -> In (r, source_occurrence_of_ref r) (visit_file fr).
  Parameter visit_file_order : forall p (fr : FileRef p),
    StronglySorted Pos.lt (map (fun rc => node_ref_local (fst rc)) (visit_file fr)).
  Parameter visit_file_nodup : forall p (fr : FileRef p),
    NoDup (map (fun rc => node_ref_local (fst rc)) (visit_file fr)).
  (* the visited syntax fragments ARE the file's canonical source occurrences, in canonical order — the
     traversal projects exactly [occurrences_file] on the second component (downstream semantic elaboration folds the
     paired syntax without a per-node search). *)
  Parameter visit_file_snd : forall p (fr : FileRef p),
    map snd (visit_file fr) = map snd (occurrences_file (file_ref_source fr)).
  (* the FULL (local-id, occurrence) correspondence: the traversal's minted local ids AND syntax fragments ARE
     the source's canonical occurrence enumeration [occurrences_file] — so a file's visit stream depends only on its
     [Syntax.File], the foundation for cross-snapshot report/fact determinism. *)
  Parameter visit_file_idocc : forall p (fr : FileRef p),
    map (fun rc => (node_ref_local (fst rc), snd rc)) (visit_file fr) = occurrences_file (file_ref_source fr).
End SNAPSHOT_SIG.

Module Snapshot : SNAPSHOT_SIG.

(* a file-root handle for ONE file occurrence of program [p]: the file's PATH (its public identity) + its
   source + a STANDARD-MAP membership proof.  No hidden slot: the path IS the map key. *)
Record FileRefRepresentation (p : Syntax.Program) := MakeFileRef {
  file_ref_path   : FilePath.T;
  file_ref_source : Syntax.File;
  file_ref_at     : FileMap.find file_ref_path (Syntax.files p) = Some file_ref_source
}.
Arguments file_ref_path   {p} _.
Arguments file_ref_source {p} _.
Arguments file_ref_at     {p} _.
Definition FileRef := FileRefRepresentation.

Record NodeRefRepresentation (p : Syntax.Program) := MakeNodeRef {
  node_ref_file  : FileRef p;
  node_ref_local : positive;
  node_ref_valid : valid_localb (file_ref_source node_ref_file) node_ref_local = true
}.
Arguments node_ref_file  {p} _.
Arguments node_ref_local {p} _.
Arguments node_ref_valid {p} _.
Definition NodeRef := NodeRefRepresentation.

Definition node_ref_key {p} (r : NodeRef p) : Key :=
  MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
Theorem node_ref_key_eq {p} (r : NodeRef p) :
  node_ref_key r = MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
Proof. reflexivity. Qed.

Record SyntaxRepresentation (p : Syntax.Program) := MakeSyntax {
  outer : FileMap.t File;
  valid    : outer = outer_of (Syntax.files p)
}.
Arguments outer {p} _.
Arguments valid    {p} _.
Definition Syntax := SyntaxRepresentation.
Definition index_program (p : Syntax.Program) : Syntax p :=
  MakeSyntax p (outer_of (Syntax.files p)) eq_refl.

Lemma valid_at {p} (idx : Syntax p) path f :
  FileMap.find path (Syntax.files p) = Some f ->
  FileMap.find path (outer idx) = Some (build_file f).
Proof. intros H. rewrite (valid idx). apply outer_get_at. exact H. Qed.

Definition ref_file_index_opt {p} (idx : Syntax p) (r : NodeRef p) : option File :=
  FileMap.find (file_ref_path (node_ref_file r)) (outer idx).
Lemma ref_file_index_some {p} (idx : Syntax p) (r : NodeRef p) :
  ref_file_index_opt idx r = Some (build_file (file_ref_source (node_ref_file r))).
Proof. unfold ref_file_index_opt. apply (valid_at idx). apply (file_ref_at (node_ref_file r)). Qed.
Lemma ref_file_index_some' {p} (idx : Syntax p) (r : NodeRef p) : ref_file_index_opt idx r <> None.
Proof. rewrite ref_file_index_some. discriminate. Qed.
Definition ref_file_index {p} (idx : Syntax p) (r : NodeRef p) : File :=
  option_get (ref_file_index_opt idx r) (ref_file_index_some' idx r).
Lemma ref_file_index_eq {p} (idx : Syntax p) (r : NodeRef p) :
  ref_file_index idx r = build_file (file_ref_source (node_ref_file r)).
Proof. unfold ref_file_index. apply option_get_eq, ref_file_index_some. Qed.

Definition ref_meta_opt {p} (idx : Syntax p) (r : NodeRef p) : option Meta :=
  Table.get (node_ref_local r) (table (ref_file_index idx r)).
Lemma ref_meta_some {p} (idx : Syntax p) (r : NodeRef p) : ref_meta_opt idx r <> None.
Proof.
  unfold ref_meta_opt. rewrite ref_file_index_eq.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r)))));
    [discriminate | discriminate Hv].
Qed.

Definition ref_meta {p} (idx : Syntax p) (r : NodeRef p) : Meta :=
  option_get (ref_meta_opt idx r) (ref_meta_some idx r).

Lemma ref_meta_spec {p} (idx : Syntax p) (r : NodeRef p) m :
  Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r)))) = Some m ->
  ref_meta idx r = m.
Proof. intros H. unfold ref_meta. apply option_get_eq. unfold ref_meta_opt. rewrite ref_file_index_eq. exact H. Qed.

Definition node_kind        {p} (idx : Syntax p) (r : NodeRef p) : Kind := kind (ref_meta idx r).
Definition node_role        {p} (idx : Syntax p) (r : NodeRef p) : Role   := role (ref_meta idx r).
Definition node_subtree_end {p} (idx : Syntax p) (r : NodeRef p) : positive   := subtree_end (ref_meta idx r).
Definition containing_file {p} (r : NodeRef p) : FileRef p := node_ref_file r.

Lemma ref_meta_get {p} (idx : Syntax p) (r : NodeRef p) :
  Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [| discriminate Hv].
  rewrite (ref_meta_spec idx r m E). reflexivity.
Qed.

Lemma parent_valid {p} (idx : Syntax p) (r : NodeRef p) pid :
  parent (ref_meta idx r) = Some pid -> valid_localb (file_ref_source (node_ref_file r)) pid = true.
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

Definition parent_of {p} (idx : Syntax p) (r : NodeRef p) : option (NodeRef p) :=
  (match parent (ref_meta idx r) as o return (parent (ref_meta idx r) = o -> option (NodeRef p)) with
   | Some pid => fun H => Some (MakeNodeRef p (node_ref_file r) pid (parent_valid idx r pid H))
   | None     => fun _ => None
   end) eq_refl.

Lemma child_valid (f : Syntax.File) local c :
  In c (child_ids (table (build_file f)) local) -> valid_localb f c = true.
Proof.
  intros Hin. unfold child_ids in Hin.
  destruct (Table.get local (table (build_file f))) as [m|] eqn:El; [|destruct Hin].
  apply child_enum_sound in Hin. unfold parent_id in Hin.
  unfold valid_localb. destruct (Table.get c (table (build_file f))); [reflexivity | discriminate Hin].
Qed.

Fixpoint refine_children {p} (fr : FileRef p) (ids : list positive)
  : (forall c, In c ids -> valid_localb (file_ref_source fr) c = true) -> list (NodeRef p) :=
  match ids with
  | []        => fun _    => []
  | c :: rest => fun Hall =>
      MakeNodeRef p fr c (Hall c (or_introl eq_refl)) :: refine_children fr rest (fun c' H => Hall c' (or_intror H))
  end.

Lemma children_valid {p} (idx : Syntax p) (r : NodeRef p) c :
  In c (child_ids (table (ref_file_index idx r)) (node_ref_local r)) ->
  valid_localb (file_ref_source (node_ref_file r)) c = true.
Proof. rewrite ref_file_index_eq. apply child_valid. Qed.

Definition children_of {p} (idx : Syntax p) (r : NodeRef p) : list (NodeRef p) :=
  refine_children (node_ref_file r)
    (child_ids (table (ref_file_index idx r)) (node_ref_local r)) (children_valid idx r).

Definition file_of_path (p : Syntax.Program) (fp : FilePath.T) : option (FileRef p) :=
  (match FileMap.find fp (Syntax.files p) as o
         return (FileMap.find fp (Syntax.files p) = o -> option (FileRef p)) with
   | Some f => fun H => Some (MakeFileRef p fp f H)
   | None   => fun _ => None
   end) eq_refl.

Definition valid_in_index {p} (idx : Syntax p) (fr : FileRef p) (local : positive) : bool :=
  match FileMap.find (file_ref_path fr) (outer idx) with
  | Some fi => match Table.get local (table fi) with Some _ => true | None => false end
  | None    => false
  end.
Lemma valid_in_index_eq {p} (idx : Syntax p) (fr : FileRef p) (local : positive) :
  valid_in_index idx fr local = valid_localb (file_ref_source fr) local.
Proof.
  unfold valid_in_index, valid_localb.
  rewrite (valid_at idx (file_ref_path fr) (file_ref_source fr) (file_ref_at fr)). reflexivity.
Qed.
Lemma valid_in_index_true {p} (idx : Syntax p) (fr : FileRef p) (local : positive) :
  valid_in_index idx fr local = true -> valid_localb (file_ref_source fr) local = true.
Proof. rewrite valid_in_index_eq. exact (fun H => H). Qed.

Definition ref_of_key (p : Syntax.Program) (idx : Syntax p) (k : Key) : option (NodeRef p) :=
  match file_of_path p (key_path k) with
  | Some fr =>
      (match valid_in_index idx fr (key_local k) as b
             return (valid_in_index idx fr (key_local k) = b -> option (NodeRef p)) with
       | true  => fun H => Some (MakeNodeRef p fr (key_local k) (valid_in_index_true idx fr (key_local k) H))
       | false => fun _ => None
       end) eq_refl
  | None => None
  end.

(* --- lift EXACT source-occurrence correspondence through the sealed reference API. --- *)

Lemma source_occ_of_ref_some {p} (r : NodeRef p) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r) <> None.
Proof.
  pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv.
  destruct (Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r))))) as [m|] eqn:E;
    [|discriminate Hv].
  destruct (meta_source_occurrence _ _ _ E) as [o [Ho _]]. rewrite Ho. discriminate.
Qed.

Definition source_occurrence_of_ref {p} (r : NodeRef p) : Occurrence :=
  option_get (source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r))
             (source_occ_of_ref_some r).

Lemma source_occ_of_ref_eq {p} (r : NodeRef p) :
  source_occurrence_at (file_ref_source (node_ref_file r)) (node_ref_local r)
    = Some (source_occurrence_of_ref r).
Proof. unfold source_occurrence_of_ref. apply option_get_some. Qed.

Theorem ref_meta_matches_source {p} (idx : Syntax p) (r : NodeRef p) :
  ref_meta idx r = occurrence_meta (source_occurrence_of_ref r).
Proof.
  pose proof (ref_meta_get idx r) as Hget.
  pose proof (build_file_source_exact (file_ref_source (node_ref_file r)) (node_ref_local r)) as HE.
  rewrite (source_occ_of_ref_eq r) in HE. cbn [option_map] in HE.
  rewrite Hget in HE. injection HE as HEq. exact HEq.
Qed.

Theorem node_kind_matches_source {p} (idx : Syntax p) (r : NodeRef p) :
  node_kind idx r = occurrence_kind (source_occurrence_of_ref r).
Proof. unfold node_kind. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_role_matches_source {p} (idx : Syntax p) (r : NodeRef p) :
  node_role idx r = occurrence_role (source_occurrence_of_ref r).
Proof. unfold node_role. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_parent_matches_source {p} (idx : Syntax p) (r : NodeRef p) :
  parent (ref_meta idx r) = occurrence_parent (source_occurrence_of_ref r).
Proof. rewrite ref_meta_matches_source. reflexivity. Qed.
Theorem node_subtree_end_matches_source {p} (idx : Syntax p) (r : NodeRef p) :
  node_subtree_end idx r = occurrence_subtree_end (source_occurrence_of_ref r).
Proof. unfold node_subtree_end. rewrite ref_meta_matches_source. reflexivity. Qed.

Definition node_at {p} (r : NodeRef p) : option Syntax.Expr := view_expr (source_occurrence_of_ref r).
Theorem node_at_matches_source_view {p} (r : NodeRef p) :
  node_at r = view_expr (source_occurrence_of_ref r).
Proof. reflexivity. Qed.

(* --- reference extensionality (validity + membership proofs are irrelevant). --- *)

Lemma node_ref_ext (p : Syntax.Program) (r1 r2 : NodeRef p) :
  node_ref_file r1 = node_ref_file r2 -> node_ref_local r1 = node_ref_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; simpl; intros -> ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma file_ref_ext (p : Syntax.Program) (fr1 fr2 : FileRef p) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [p1 f1 h1], fr2 as [p2 f2 h2]; simpl; intros Hp. subst p2.
  assert (f1 = f2) by (pose proof h1 as q; rewrite h2 in q; injection q as <-; reflexivity).
  subst f2. f_equal. apply (UIP_dec optional_source_file_eq_dec).
Qed.

(* --- total-API correctness. --- *)

Theorem node_kind_spec (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  node_kind idx r = kind (ref_meta idx r).
Proof. reflexivity. Qed.
Theorem node_role_spec (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  node_role idx r = role (ref_meta idx r).
Proof. reflexivity. Qed.
Theorem ref_meta_built (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  Table.get (node_ref_local r) (table (build_file (file_ref_source (node_ref_file r)))) = Some (ref_meta idx r).
Proof. apply ref_meta_get. Qed.
Theorem containing_file_spec (p : Syntax.Program) (r : NodeRef p) :
  containing_file r = node_ref_file r /\ file_ref_path (containing_file r) = key_path (node_ref_key r).
Proof. split; reflexivity. Qed.

Lemma parent_of_none (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  parent (ref_meta idx r) = None -> parent_of idx r = None.
Proof.
  intros Hn. unfold parent_of. generalize (@eq_refl (option positive) (parent (ref_meta idx r))).
  destruct (parent (ref_meta idx r)) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

Lemma parent_of_some (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) pid :
  parent (ref_meta idx r) = Some pid ->
  exists pr, parent_of idx r = Some pr
             /\ node_ref_file pr = node_ref_file r /\ node_ref_local pr = pid.
Proof.
  intros Hs. unfold parent_of. generalize (@eq_refl (option positive) (parent (ref_meta idx r))).
  destruct (parent (ref_meta idx r)) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | cbn; congruence]].
  - congruence.
Qed.

Theorem parent_root (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  node_ref_local r = root_id -> parent_of idx r = None.
Proof.
  intros Hr. apply parent_of_none.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  destruct (sub_root WF) as [m0 [Hg [Hp0 _]]]. pose proof (ref_meta_get idx r) as Hget.
  rewrite Hr, Hg in Hget. injection Hget as Heq. rewrite <- Heq. exact Hp0.
Qed.

Theorem parent_nonroot (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  node_ref_local r <> root_id -> exists pr, parent_of idx r = Some pr.
Proof.
  intros Hne.
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_prng WF (node_ref_local r) (ref_meta idx r) ltac:(lia) Hhi Hget) as [q [mq [Hpar _]]].
  destruct (parent_of_some p idx r q Hpar) as [pr [Hpr _]]. exists pr. exact Hpr.
Qed.

Theorem node_parent_ref_matches_source (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  match occurrence_parent (source_occurrence_of_ref r) with
  | None     => parent_of idx r = None
  | Some pid => exists pr, parent_of idx r = Some pr /\ node_ref_local pr = pid
  end.
Proof.
  rewrite <- (node_parent_matches_source idx r).
  destruct (parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some p idx r pid Hp) as [pr [Hpr [_ Hpl]]]. exists pr. split; [exact Hpr | exact Hpl].
  - apply (parent_of_none p idx r Hp).
Qed.

Theorem node_ref_key_inj (p : Syntax.Program) (r1 r2 : NodeRef p) :
  node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  intros H. unfold node_ref_key in H. injection H as Hpath Hlocal.
  apply node_ref_ext; [ apply file_ref_ext; exact Hpath | exact Hlocal ].
Qed.

Theorem parent_same_file (p : Syntax.Program) (idx : Syntax p) (r pr : NodeRef p) :
  parent_of idx r = Some pr -> node_ref_file pr = node_ref_file r.
Proof.
  intros H. destruct (parent (ref_meta idx r)) as [pid|] eqn:Hp.
  - destruct (parent_of_some p idx r pid Hp) as [pr' [Hpr' [Hf _]]].
    rewrite H in Hpr'. injection Hpr' as <-. exact Hf.
  - rewrite (parent_of_none p idx r Hp) in H. discriminate H.
Qed.

Lemma refine_children_file (p : Syntax.Program) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> node_ref_file cr = fr.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [reflexivity | eapply IH; exact Hin].
Qed.
Theorem children_same_file (p : Syntax.Program) (idx : Syntax p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> node_ref_file cr = node_ref_file r.
Proof. unfold children_of. apply refine_children_file. Qed.

Lemma refine_children_local (p : Syntax.Program) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) cr :
  In cr (refine_children fr ids H) -> In (node_ref_local cr) ids.
Proof.
  revert H. induction ids as [|c rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.
Lemma refine_children_complete (p : Syntax.Program) (fr : FileRef p) ids
  (H : forall c, In c ids -> valid_localb (file_ref_source fr) c = true) c :
  In c ids -> exists cr, In cr (refine_children fr ids H) /\ node_ref_local cr = c.
Proof.
  revert H. induction ids as [|c0 rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [->|Hin].
  - eexists. split; [left; reflexivity | reflexivity].
  - destruct (IH (fun c' Hc' => H c' (or_intror Hc')) Hin) as [cr [Hcr Hl]].
    exists cr. split; [right; exact Hcr | exact Hl].
Qed.

Theorem children_sound (p : Syntax.Program) (idx : Syntax p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> In (node_ref_local cr) (child_ids (table (ref_file_index idx r)) (node_ref_local r)).
Proof. unfold children_of. apply refine_children_local. Qed.

Lemma refine_children_map_local (p : Syntax.Program) (fr : FileRef p) ids
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

Theorem children_of_source_order (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  StronglySorted Pos.lt (map node_ref_local (children_of idx r)).
Proof.
  unfold children_of. rewrite refine_children_map_local, (ref_file_index_eq idx r). apply children_sorted.
Qed.

Theorem children_of_nodup (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  NoDup (children_of idx r).
Proof.
  apply (NoDup_map_inv node_ref_local). apply sorted_lt_nodup. apply children_of_source_order.
Qed.

Lemma file_of_path_path (p : Syntax.Program) (fp : FilePath.T) (fr : FileRef p) :
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof.
  unfold file_of_path. generalize (@eq_refl (option Syntax.File) (FileMap.find fp (Syntax.files p))).
  destruct (FileMap.find fp (Syntax.files p)) as [f|] at 2 3; intros e H; [| discriminate H].
  injection H as <-. reflexivity.
Qed.

Theorem ref_of_key_sound (p : Syntax.Program) (idx : Syntax p) (k : Key) (r : NodeRef p) :
  ref_of_key p idx k = Some r -> node_ref_key r = k.
Proof.
  unfold ref_of_key. destruct (file_of_path p (key_path k)) as [fr|] eqn:Ef; [| discriminate].
  generalize (@eq_refl bool (valid_in_index idx fr (key_local k))).
  destruct (valid_in_index idx fr (key_local k)) at 2 3; intros e H; [| discriminate H].
  injection H as <-. unfold node_ref_key. simpl.
  rewrite (file_of_path_path p (key_path k) fr Ef). destruct k; reflexivity.
Qed.

Lemma file_of_path_complete (p : Syntax.Program) (fr : FileRef p) :
  file_of_path p (file_ref_path fr) = Some fr.
Proof.
  unfold file_of_path.
  generalize (@eq_refl (option Syntax.File) (FileMap.find (file_ref_path fr) (Syntax.files p))).
  destruct (FileMap.find (file_ref_path fr) (Syntax.files p)) as [f|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - exfalso. rewrite (file_ref_at fr) in e. discriminate e.
Qed.

Theorem ref_of_key_complete (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  ref_of_key p idx (node_ref_key r) = Some r.
Proof.
  unfold ref_of_key, node_ref_key. cbn [key_path key_local].
  rewrite (file_of_path_complete p (node_ref_file r)).
  generalize (@eq_refl bool (valid_in_index idx (node_ref_file r) (node_ref_local r))).
  destruct (valid_in_index idx (node_ref_file r) (node_ref_local r)) at 2 3; intros e.
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. rewrite valid_in_index_eq, (node_ref_valid r) in e. discriminate e.
Qed.

Theorem file_of_path_source (p : Syntax.Program) (path : FilePath.T) (f : Syntax.File) :
  find_file path (Syntax.files p) = Some f ->
  exists fr, file_of_path p path = Some fr /\ file_ref_path fr = path /\ file_ref_source fr = f.
Proof.
  intros Hfind. exists (MakeFileRef p path f Hfind). split; [| split; reflexivity].
  unfold file_of_path.
  generalize (@eq_refl (option Syntax.File) (FileMap.find path (Syntax.files p))).
  destruct (FileMap.find path (Syntax.files p)) as [f'|] at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - unfold find_file in Hfind. rewrite Hfind in e. discriminate e.
Qed.

Theorem ref_of_key_source (p : Syntax.Program) (idx : Syntax p) (path : FilePath.T) (f : Syntax.File) (local : positive) :
  find_file path (Syntax.files p) = Some f -> valid_localb f local = true ->
  exists r, ref_of_key p idx (MakeKey path local) = Some r
            /\ node_ref_local r = local /\ file_ref_source (node_ref_file r) = f.
Proof.
  intros Hfind Hv.
  destruct (file_of_path_source p path f Hfind) as [fr [Hfp [_ Hff]]].
  assert (Hvi : valid_in_index idx fr local = true) by (rewrite valid_in_index_eq, Hff; exact Hv).
  unfold ref_of_key. cbn [key_path key_local]. rewrite Hfp.
  generalize (@eq_refl bool (valid_in_index idx fr local)).
  destruct (valid_in_index idx fr local) at 2 3; intros e.
  - eexists. split; [reflexivity | split; [reflexivity | exact Hff]].
  - rewrite Hvi in e. discriminate e.
Qed.

Theorem file_ref_path_inj (p : Syntax.Program) (fr1 fr2 : FileRef p) :
  file_ref_path fr1 = file_ref_path fr2 -> fr1 = fr2.
Proof. apply file_ref_ext. Qed.

Theorem child_parent (p : Syntax.Program) (idx : Syntax p) (r cr : NodeRef p) :
  In cr (children_of idx r) -> parent_of idx cr = Some r.
Proof.
  intros Hin.
  pose proof (children_same_file p idx r cr Hin) as Hf.
  pose proof (children_sound p idx r cr Hin) as Hsound.
  apply child_ids_parent in Hsound.
  pose proof (ref_meta_get idx cr) as Hget.
  rewrite Hf in Hget. rewrite <- (ref_file_index_eq idx r) in Hget.
  unfold parent_id in Hsound. rewrite Hget in Hsound.
  destruct (parent_of_some p idx cr (node_ref_local r) Hsound) as [pr [Hpr [Hpf Hpl]]].
  rewrite Hpr. f_equal. apply node_ref_ext; [ rewrite Hpf; exact Hf | exact Hpl ].
Qed.

Theorem parent_child (p : Syntax.Program) (idx : Syntax p) (r pr : NodeRef p) :
  parent_of idx r = Some pr -> In r (children_of idx pr).
Proof.
  intros Hpar.
  pose proof (parent_same_file p idx r pr Hpar) as Hf.
  assert (Hp' : parent (ref_meta idx r) = Some (node_ref_local pr)).
  { destruct (parent (ref_meta idx r)) as [pid|] eqn:Hnp.
    - destruct (parent_of_some p idx r pid Hnp) as [pr' [Hpr' [_ Hpl]]].
      rewrite Hpar in Hpr'. injection Hpr' as <-. rewrite Hpl. reflexivity.
    - rewrite (parent_of_none p idx r Hnp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx r) as Hgetr. rewrite <- Hf in Hgetr.
  pose proof (parent_has_child (file_ref_source (node_ref_file pr))
                (node_ref_local pr) (node_ref_local r) (ref_meta idx r) Hgetr Hp') as Hchild.
  rewrite <- (ref_file_index_eq idx pr) in Hchild.
  destruct (refine_children_complete p (node_ref_file pr)
              (child_ids (table (ref_file_index idx pr)) (node_ref_local pr))
              (children_valid idx pr) (node_ref_local r) Hchild) as [cr [Hcr Hcl]].
  pose proof (refine_children_file p (node_ref_file pr) _ (children_valid idx pr) cr Hcr) as Hcrf.
  assert (Hcreq : cr = r).
  { apply node_ref_ext; [ rewrite Hcrf, Hf; reflexivity | rewrite Hcl; reflexivity ]. }
  subst cr. unfold children_of. exact Hcr.
Qed.

(* --- NodeRef-level ancestry: the O(1) interval test, certified through the sealed API. --- *)

Lemma ref_file_index_table_same_file (p : Syntax.Program) (idx : Syntax p) (x y : NodeRef p) :
  node_ref_file x = node_ref_file y -> table (ref_file_index idx x) = table (ref_file_index idx y).
Proof. intros H. rewrite (ref_file_index_eq idx x), (ref_file_index_eq idx y), H. reflexivity. Qed.

Lemma parentof_to_parentid (p : Syntax.Program) (idx : Syntax p) (d a : NodeRef p) :
  parent_of idx d = Some a ->
  node_ref_file a = node_ref_file d /\
  parent_id (table (ref_file_index idx d)) (node_ref_local d) = Some (node_ref_local a).
Proof.
  intros Hpar. pose proof (parent_same_file p idx d a Hpar) as Hf. split; [exact Hf|].
  assert (Hnp : parent (ref_meta idx d) = Some (node_ref_local a)).
  { destruct (parent (ref_meta idx d)) as [pid|] eqn:Hp.
    - destruct (parent_of_some p idx d pid Hp) as [a' [Ha' [_ Hal]]].
      rewrite Hpar in Ha'. injection Ha' as <-. rewrite Hal. reflexivity.
    - rewrite (parent_of_none p idx d Hp) in Hpar. discriminate Hpar. }
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_file_index_eq idx d) in Hget.
  unfold parent_id. rewrite Hget. exact Hnp.
Qed.

Lemma parentid_to_parentof (p : Syntax.Program) (idx : Syntax p) (d : NodeRef p) pa :
  parent_id (table (ref_file_index idx d)) (node_ref_local d) = Some pa ->
  exists a, parent_of idx d = Some a /\ node_ref_local a = pa /\ node_ref_file a = node_ref_file d.
Proof.
  intros Hpid.
  pose proof (ref_meta_get idx d) as Hget. rewrite <- (ref_file_index_eq idx d) in Hget.
  unfold parent_id in Hpid. rewrite Hget in Hpid.
  destruct (parent_of_some p idx d pa Hpid) as [a [Ha [Hf Hal]]].
  exists a. split; [exact Ha | split; [exact Hal | exact Hf]].
Qed.

Inductive RefAncestor (p : Syntax.Program) (idx : Syntax p) : NodeRef p -> NodeRef p -> Prop :=
| RAnc_dir  : forall a d, parent_of idx d = Some a -> RefAncestor p idx a d
| RAnc_step : forall a q d, RefAncestor p idx a q -> parent_of idx d = Some q -> RefAncestor p idx a d.

Lemma refanc_same_file (p : Syntax.Program) (idx : Syntax p) (a d : NodeRef p) :
  RefAncestor p idx a d -> node_ref_file a = node_ref_file d.
Proof.
  intros H. induction H as [a d Hpar | a q d Hanc IH Hpar].
  - apply (proj1 (parentof_to_parentid p idx d a Hpar)).
  - rewrite IH. apply (proj1 (parentof_to_parentid p idx d q Hpar)).
Qed.

Lemma refanc_to_anc (p : Syntax.Program) (idx : Syntax p) (a d : NodeRef p) :
  RefAncestor p idx a d -> Ancestor (table (ref_file_index idx d)) (node_ref_local a) (node_ref_local d).
Proof.
  intros H. induction H as [a d Hpar | a q d Hanc IH Hpar].
  - apply Anc_dir. apply (proj2 (parentof_to_parentid p idx d a Hpar)).
  - pose proof (proj1 (parentof_to_parentid p idx d q Hpar)) as Hf.
    rewrite (ref_file_index_table_same_file p idx q d Hf) in IH.
    apply (Anc_step (table (ref_file_index idx d)) (node_ref_local a) (node_ref_local q) (node_ref_local d) IH).
    apply (proj2 (parentof_to_parentid p idx d q Hpar)).
Qed.

Lemma ancestor_to_ref_ancestor_aux (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) (al dl : positive)
  (Hanc : Ancestor (table (build_file (file_ref_source fr))) al dl) :
  forall (d : NodeRef p), node_ref_file d = fr -> node_ref_local d = dl ->
  exists a, node_ref_file a = fr /\ node_ref_local a = al /\ RefAncestor p idx a d.
Proof.
  induction Hanc as [al dl Hpid | al pl dl Hanc_ap IH Hpid_d]; intros d Hdf Hdl.
  - assert (Hpd : parent_id (table (ref_file_index idx d)) (node_ref_local d) = Some al)
      by (rewrite (ref_file_index_eq idx d), Hdf, Hdl; exact Hpid).
    destruct (parentid_to_parentof p idx d al Hpd) as [a [Ha [Hal Haf]]].
    exists a. split; [rewrite Haf; exact Hdf | split; [exact Hal | apply RAnc_dir; exact Ha]].
  - assert (Hpd : parent_id (table (ref_file_index idx d)) (node_ref_local d) = Some pl)
      by (rewrite (ref_file_index_eq idx d), Hdf, Hdl; exact Hpid_d).
    destruct (parentid_to_parentof p idx d pl Hpd) as [pr [Hp [Hpl Hpf]]].
    destruct (IH pr (eq_trans Hpf Hdf) Hpl) as [a [Haf [Hal Hra]]].
    exists a. split; [exact Haf | split; [exact Hal | apply (RAnc_step p idx a pr d Hra Hp)]].
Qed.

Lemma ancestor_to_ref_ancestor (p : Syntax.Program) (idx : Syntax p) (a d : NodeRef p) :
  node_ref_file a = node_ref_file d ->
  Ancestor (table (build_file (file_ref_source (node_ref_file d)))) (node_ref_local a) (node_ref_local d) ->
  RefAncestor p idx a d.
Proof.
  intros Hf Hanc.
  destruct (ancestor_to_ref_ancestor_aux p idx (node_ref_file d) (node_ref_local a) (node_ref_local d) Hanc d eq_refl eq_refl)
    as [a' [Haf [Hal Hra]]].
  assert (a' = a) by (apply node_ref_ext; [ rewrite Haf; symmetry; exact Hf | exact Hal ]).
  subst a'. exact Hra.
Qed.

Definition is_ancestor_ref {p} (idx : Syntax p) (a d : NodeRef p) : bool :=
  FilePath.equalb (file_ref_path (node_ref_file a)) (file_ref_path (node_ref_file d)) &&
  is_ancestor_local (table (ref_file_index idx d)) (node_ref_local a) (node_ref_local d).

Lemma ref_local_present (p : Syntax.Program) (idx : Syntax p) (a d : NodeRef p) :
  node_ref_file a = node_ref_file d ->
  Table.get (node_ref_local a) (table (build_file (file_ref_source (node_ref_file d)))) <> None.
Proof.
  intros Hf. rewrite <- Hf. pose proof (ref_meta_get idx a) as Hg. rewrite Hg. discriminate.
Qed.

Theorem ref_ancestry (p : Syntax.Program) (idx : Syntax p) (a d : NodeRef p) :
  is_ancestor_ref idx a d = true <-> RefAncestor p idx a d.
Proof.
  unfold is_ancestor_ref. split.
  - intros Hb. apply andb_true_iff in Hb as [Hpath Hloc]. apply FilePath.equalb_spec in Hpath.
    assert (Hf : node_ref_file a = node_ref_file d) by (apply file_ref_ext; exact Hpath).
    apply (ancestor_to_ref_ancestor p idx a d Hf).
    rewrite (ref_file_index_eq idx d) in Hloc.
    apply (proj1 (interval_ancestry (file_ref_source (node_ref_file d))
                    (node_ref_local a) (node_ref_local d) (ref_local_present p idx a d Hf))).
    exact Hloc.
  - intros Hra.
    pose proof (refanc_same_file p idx a d Hra) as Hf.
    pose proof (refanc_to_anc p idx a d Hra) as Hanc.
    apply andb_true_iff. split.
    + apply FilePath.equalb_spec. rewrite Hf. reflexivity.
    + rewrite (ref_file_index_eq idx d). rewrite (ref_file_index_eq idx d) in Hanc.
      apply (proj2 (interval_ancestry (file_ref_source (node_ref_file d))
                      (node_ref_local a) (node_ref_local d) (ref_local_present p idx a d Hf))).
      exact Hanc.
Qed.

(* --- minting soundness for FileRef + the rejection cases. --- *)

Theorem file_of_path_sound (p : Syntax.Program) (fp : FilePath.T) (fr : FileRef p) :
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof. apply file_of_path_path. Qed.

(* the SOURCE a minted FileRef carries is EXACTLY the program's map binding at the queried path. *)
Theorem file_of_path_source_exact (p : Syntax.Program) (fp : FilePath.T) (fr : FileRef p) :
  file_of_path p fp = Some fr -> find_file fp (Syntax.files p) = Some (file_ref_source fr).
Proof.
  intros H. pose proof (file_of_path_path p fp fr H) as Hpath.
  pose proof (file_ref_at fr) as Hat. rewrite Hpath in Hat. exact Hat.
Qed.

Lemma file_of_path_none (p : Syntax.Program) (fp : FilePath.T) :
  FileMap.find fp (Syntax.files p) = None -> file_of_path p fp = None.
Proof.
  intros H. unfold file_of_path.
  generalize (@eq_refl (option Syntax.File) (FileMap.find fp (Syntax.files p))).
  destruct (FileMap.find fp (Syntax.files p)) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

Theorem ref_of_key_invalid_path (p : Syntax.Program) (idx : Syntax p) (fp : FilePath.T) (local : positive) :
  find_file fp (Syntax.files p) = None -> ref_of_key p idx (MakeKey fp local) = None.
Proof.
  intros H. unfold ref_of_key. cbn [key_path key_local].
  rewrite (file_of_path_none p fp H). reflexivity.
Qed.

Theorem ref_of_key_invalid_local (p : Syntax.Program) (idx : Syntax p) (fp : FilePath.T) (f : Syntax.File) (local : positive) :
  find_file fp (Syntax.files p) = Some f -> valid_localb f local = false -> ref_of_key p idx (MakeKey fp local) = None.
Proof.
  intros Hf Hv. destruct (file_of_path_source p fp f Hf) as [fr [Hfp [_ Hfs]]].
  assert (Hvi : valid_in_index idx fr local = false) by (rewrite valid_in_index_eq, Hfs; exact Hv).
  unfold ref_of_key. cbn [key_path key_local]. rewrite Hfp.
  generalize (@eq_refl bool (valid_in_index idx fr local)).
  destruct (valid_in_index idx fr local) at 2 3; intros e; [ congruence | reflexivity ].
Qed.

(* --- decidable NodeRef equality: reference identity IS Key identity. --- *)

Definition noderef_eq_dec {p} (r1 r2 : NodeRef p) : {r1 = r2} + {r1 <> r2}.
Proof.
  destruct (key_eq_dec (node_ref_key r1) (node_ref_key r2)) as [Heq|Hne].
  - left. apply node_ref_key_inj. exact Heq.
  - right. intro H. apply Hne. rewrite H. reflexivity.
Defined.

(* --- the file-root reference + the canonical preorder enumeration of ALL a file's references. --- *)

Definition file_root_ref {p} (fr : FileRef p) : NodeRef p :=
  MakeNodeRef p fr root_id (root_valid (file_ref_source fr)).
Lemma file_root_ref_local (p : Syntax.Program) (fr : FileRef p) : node_ref_local (file_root_ref fr) = root_id.
Proof. reflexivity. Qed.
Lemma file_root_ref_file (p : Syntax.Program) (fr : FileRef p) : node_ref_file (file_root_ref fr) = fr.
Proof. reflexivity. Qed.

(* the FileRef-level index accessor: ONE outer-map lookup into the PRECOMPUTED [outer idx] — it REUSES the
   passed Syntax and does NOT rebuild [build_file].  Provably equal to the file's build for the proofs. *)
Definition file_index_opt {p} (idx : Syntax p) (fr : FileRef p) : option File :=
  FileMap.find (file_ref_path fr) (outer idx).
Lemma file_index_some {p} (idx : Syntax p) (fr : FileRef p) :
  file_index_opt idx fr = Some (build_file (file_ref_source fr)).
Proof. unfold file_index_opt. apply (valid_at idx). apply (file_ref_at fr). Qed.
Lemma file_index_some' {p} (idx : Syntax p) (fr : FileRef p) : file_index_opt idx fr <> None.
Proof. rewrite file_index_some. discriminate. Qed.
Definition file_index {p} (idx : Syntax p) (fr : FileRef p) : File :=
  option_get (file_index_opt idx fr) (file_index_some' idx fr).
Lemma file_index_eq {p} (idx : Syntax p) (fr : FileRef p) : file_index idx fr = build_file (file_ref_source fr).
Proof. unfold file_index. apply option_get_eq, file_index_some. Qed.

Lemma all_ids_valid_idx {p} (idx : Syntax p) (fr : FileRef p) :
  forall c, In c (all_ids (file_index idx fr)) -> valid_localb (file_ref_source fr) c = true.
Proof. rewrite (file_index_eq idx fr). apply all_ids_valid. Qed.

(* the canonical preorder enumeration of ALL a file's references, reusing the precomputed File. *)
Definition file_refs {p} (idx : Syntax p) (fr : FileRef p) : list (NodeRef p) :=
  refine_children fr (all_ids (file_index idx fr)) (all_ids_valid_idx idx fr).

Theorem file_refs_same_file (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) (r : NodeRef p) :
  In r (file_refs idx fr) -> node_ref_file r = fr.
Proof. unfold file_refs. apply refine_children_file. Qed.

Lemma file_refs_map_local (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) :
  map node_ref_local (file_refs idx fr) = all_ids (file_index idx fr).
Proof. unfold file_refs. apply refine_children_map_local. Qed.

Theorem file_refs_complete (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) (r : NodeRef p) :
  node_ref_file r = fr -> In r (file_refs idx fr).
Proof.
  intros Hf. pose proof (node_ref_valid r) as Hv. unfold valid_localb in Hv. rewrite Hf in Hv.
  destruct (Table.get (node_ref_local r) (table (build_file (file_ref_source fr)))) as [m|] eqn:E;
    [|discriminate Hv].
  pose proof (enumeration_complete (file_ref_source fr) (node_ref_local r) m E) as Hin.
  rewrite <- (file_index_eq idx fr) in Hin.
  destruct (refine_children_complete p fr (all_ids (file_index idx fr))
              (all_ids_valid_idx idx fr) (node_ref_local r) Hin) as [cr [Hcr Hcl]].
  assert (Hcreq : cr = r).
  { apply node_ref_ext;
      [ rewrite (refine_children_file p fr _ (all_ids_valid_idx idx fr) cr Hcr), Hf; reflexivity
      | rewrite Hcl; reflexivity ]. }
  subst cr. exact Hcr.
Qed.

Theorem file_refs_nodup (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) : NoDup (file_refs idx fr).
Proof.
  apply (NoDup_map_inv node_ref_local). rewrite file_refs_map_local, (file_index_eq idx fr). apply pos_seq_no_duplicates.
Qed.

Theorem file_refs_source_order (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) :
  StronglySorted Pos.lt (map node_ref_local (file_refs idx fr)).
Proof. rewrite file_refs_map_local, (file_index_eq idx fr). apply pos_seq_sorted. Qed.

Theorem file_root_ref_in_refs (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) :
  In (file_root_ref fr) (file_refs idx fr).
Proof. apply file_refs_complete. reflexivity. Qed.

(* every occurrence is reachable from its file root by repeated parent links (the root is a strict ancestor
   of every non-root occurrence — the root's subtree is the whole file). *)
Theorem reachable_from_root (p : Syntax.Program) (idx : Syntax p) (r : NodeRef p) :
  node_ref_local r <> root_id -> RefAncestor p idx (file_root_ref (node_ref_file r)) r.
Proof.
  intros Hne. apply ancestor_to_ref_ancestor; [ reflexivity | ].
  cbn [node_ref_local file_root_ref].
  pose proof (build_file_wf (file_ref_source (node_ref_file r))) as WF.
  pose proof (ref_meta_get idx r) as Hget.
  destruct (in_domain (file_ref_source (node_ref_file r)) (node_ref_local r) (ref_meta idx r) Hget) as [Hlo Hhi].
  destruct (sub_root WF) as [m0 [Hgr [_ Hend]]].
  apply (sub_snd WF root_id (node_ref_local r) m0);
    [ lia | lia | exact Hgr | lia | rewrite Hend; exact Hhi ].
Qed.

(* every ENUMERATED reference is the file root or reachable from it — the enumeration is a rooted tree. *)
Theorem refs_reachable (p : Syntax.Program) (idx : Syntax p) (fr : FileRef p) (r : NodeRef p) :
  In r (file_refs idx fr) -> r = file_root_ref fr \/ RefAncestor p idx (file_root_ref fr) r.
Proof.
  intros Hin. pose proof (file_refs_same_file p idx fr r Hin) as Hf.
  destruct (Pos.eq_dec (node_ref_local r) root_id) as [Hroot|Hnroot].
  - left. apply node_ref_ext; [ rewrite Hf; reflexivity | rewrite Hroot; reflexivity ].
  - right. rewrite <- Hf. apply reachable_from_root. exact Hnroot.
Qed.

(* --- the canonical indexed traversal: mint a validated NodeRef at each structural position. --- *)

Lemma occurrences_file_valid {p} (fr : FileRef p) :
  forall id occ, In (id, occ) (occurrences_file (file_ref_source fr)) -> valid_localb (file_ref_source fr) id = true.
Proof.
  intros id occ Hin. pose proof (occurrences_file_sound (file_ref_source fr) id occ Hin) as Hs.
  unfold valid_localb. rewrite (source_occurrence_meta (file_ref_source fr) id occ Hs). reflexivity.
Qed.

Fixpoint visit_lift {p} (fr : FileRef p) (l : list (positive * Occurrence))
  : (forall id occ, In (id, occ) l -> valid_localb (file_ref_source fr) id = true) -> list (NodeRef p * Occurrence) :=
  match l with
  | [] => fun _ => []
  | (id, occ) :: rest => fun H =>
      (MakeNodeRef p fr id (H id occ (or_introl eq_refl)), occ)
        :: visit_lift fr rest (fun i o Hin => H i o (or_intror Hin))
  end.

(* the single-pass [walk_file] stream is valid (it IS [occurrences_file], which is valid). *)
Lemma walk_file_valid {p} (fr : FileRef p) :
  forall id occ, In (id, occ) (walk_file (file_ref_source fr)) -> valid_localb (file_ref_source fr) id = true.
Proof. intros id occ Hin. rewrite walk_file_eq in Hin. exact (occurrences_file_valid fr id occ Hin). Qed.

(* the indexed traversal RUNS the single-pass [walk_file] (one traversal per file, no boundary rescan). *)
Definition visit_file {p} (fr : FileRef p) : list (NodeRef p * Occurrence) :=
  visit_lift fr (walk_file (file_ref_source fr)) (walk_file_valid fr).

Lemma visit_lift_in {p} (fr : FileRef p) l H (r : NodeRef p) occ :
  In (r, occ) (visit_lift fr l H) -> node_ref_file r = fr /\ In (node_ref_local r, occ) l.
Proof.
  revert H. induction l as [|[id0 occ0] rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [node_ref_file node_ref_local]. split; [reflexivity | left; reflexivity].
  - destruct (IH (fun i o Hi => H i o (or_intror Hi)) Hin) as [Hf Hl]. split; [exact Hf | right; exact Hl].
Qed.

Lemma visit_lift_mem {p} (fr : FileRef p) l H (id : positive) (occ : Occurrence) :
  In (id, occ) l -> exists r, node_ref_file r = fr /\ node_ref_local r = id /\ In (r, occ) (visit_lift fr l H).
Proof.
  revert H. induction l as [|[id0 occ0] rest IH]; intros H Hin; simpl in Hin; [destruct Hin|].
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. exists (MakeNodeRef p fr id0 (H id0 occ0 (or_introl eq_refl))).
    cbn [node_ref_file node_ref_local]. split; [reflexivity | split; [reflexivity | left; reflexivity]].
  - destruct (IH (fun i o Hi => H i o (or_intror Hi)) Hin) as [r [Hf [Hl Hin']]].
    exists r. split; [exact Hf | split; [exact Hl | right; exact Hin']].
Qed.

Lemma visit_lift_local {p} (fr : FileRef p) l H :
  map (fun rc => node_ref_local (fst rc)) (visit_lift fr l H) = map fst l.
Proof.
  revert H. induction l as [|[id0 occ0] rest IH]; intros H; simpl; [reflexivity|].
  cbn [node_ref_local fst]. rewrite IH. reflexivity.
Qed.

Lemma visit_lift_snd {p} (fr : FileRef p) l H :
  map snd (visit_lift fr l H) = map snd l.
Proof.
  revert H. induction l as [|[id0 occ0] rest IH]; intros H; simpl; [reflexivity|].
  cbn [snd]. rewrite IH. reflexivity.
Qed.

Lemma visit_file_snd {p} (fr : FileRef p) :
  map snd (visit_file fr) = map snd (occurrences_file (file_ref_source fr)).
Proof. unfold visit_file. rewrite visit_lift_snd, walk_file_eq. reflexivity. Qed.

Lemma visit_lift_idocc {p} (fr : FileRef p) l H :
  map (fun rc => (node_ref_local (fst rc), snd rc)) (visit_lift fr l H) = l.
Proof.
  revert H. induction l as [|[id0 occ0] rest IH]; intros H; simpl; [reflexivity|].
  cbn [node_ref_local fst snd]. rewrite IH. reflexivity.
Qed.

(* the FULL (local-id, occurrence) correspondence: the reference traversal's minted local ids AND syntax
   fragments ARE the source's canonical occurrence enumeration — the pass adds only validated references. *)
Lemma visit_file_idocc {p} (fr : FileRef p) :
  map (fun rc => (node_ref_local (fst rc), snd rc)) (visit_file fr) = occurrences_file (file_ref_source fr).
Proof. unfold visit_file. rewrite visit_lift_idocc, walk_file_eq. reflexivity. Qed.

Theorem visit_file_view (p : Syntax.Program) (fr : FileRef p) (r : NodeRef p) (occ : Occurrence) :
  In (r, occ) (visit_file fr) -> occ = source_occurrence_of_ref r /\ node_ref_file r = fr.
Proof.
  intros Hin. destruct (visit_lift_in fr (walk_file (file_ref_source fr)) (walk_file_valid fr) r occ Hin) as [Hf Hl].
  split; [| exact Hf].
  rewrite walk_file_eq in Hl.
  pose proof (occurrences_file_sound (file_ref_source fr) (node_ref_local r) occ Hl) as Hs.
  pose proof (source_occ_of_ref_eq r) as He. rewrite Hf in He. rewrite Hs in He.
  injection He as He2. exact He2.
Qed.

Theorem visit_file_complete (p : Syntax.Program) (fr : FileRef p) (r : NodeRef p) :
  node_ref_file r = fr -> In (r, source_occurrence_of_ref r) (visit_file fr).
Proof.
  intros Hf.
  pose proof (source_occ_of_ref_eq r) as He. rewrite Hf in He.
  pose proof (occurrences_file_complete (file_ref_source fr) (node_ref_local r) (source_occurrence_of_ref r) He) as Hin.
  rewrite <- walk_file_eq in Hin.
  destruct (visit_lift_mem fr (walk_file (file_ref_source fr)) (walk_file_valid fr)
              (node_ref_local r) (source_occurrence_of_ref r) Hin) as [r' [Hf' [Hl' Hin']]].
  assert (Hr : r' = r) by (apply node_ref_ext; [ rewrite Hf', Hf; reflexivity | exact Hl' ]).
  subst r'. exact Hin'.
Qed.

Theorem visit_file_order (p : Syntax.Program) (fr : FileRef p) :
  StronglySorted Pos.lt (map (fun rc => node_ref_local (fst rc)) (visit_file fr)).
Proof.
  unfold visit_file. rewrite (visit_lift_local fr (walk_file (file_ref_source fr)) (walk_file_valid fr)).
  rewrite walk_file_eq. apply occurrences_file_sorted.
Qed.

Theorem visit_file_nodup (p : Syntax.Program) (fr : FileRef p) :
  NoDup (map (fun rc => node_ref_local (fst rc)) (visit_file fr)).
Proof.
  unfold visit_file. rewrite (visit_lift_local fr (walk_file (file_ref_source fr)) (walk_file_valid fr)).
  rewrite walk_file_eq. apply occurrences_file_nodup.
Qed.

End Snapshot.

(* negative ABSTRACTION checks: the raw index map and raw record constructors are NOT reachable through the
   sealed [Snapshot] interface (each [Check] FAILS, so [Fail Check] succeeds). *)
Fail Check Snapshot.MakeSyntax.
Fail Check Snapshot.MakeFileRef.
Fail Check Snapshot.MakeNodeRef.
Fail Check Snapshot.outer.
Fail Check Snapshot.ref_fi.
Fail Check Snapshot.file_index.

(** ** typed / kind-refined references.  A [NodeRefOf p k] is a [NodeRef p] whose EXACT source        *)
(* occurrence has kind [k] — the kind proof is tied to [source_occurrence_of_ref] (via                   *)
(* [node_kind_matches_source]), NOT an author-supplied boolean.  Erasure recovers the underlying ref;    *)
(* the erased Key determines the typed-ref identity (no second identity system).                     *)

Definition NodeRefOf (p : Syntax.Program) (k : Kind) : Type :=
  { r : Snapshot.NodeRef p | occurrence_kind (Snapshot.source_occurrence_of_ref r) = k }.
Definition erase_ref {p k} (tr : NodeRefOf p k) : Snapshot.NodeRef p := proj1_sig tr.
Definition FileNodeRef      (p : Syntax.Program) := NodeRefOf p FileKind.
Definition PackageClauseRef (p : Syntax.Program) := NodeRefOf p PackageClauseKind.
Definition DeclRef          (p : Syntax.Program) := NodeRefOf p DeclarationKind.
Definition StmtRef          (p : Syntax.Program) := NodeRefOf p StatementKind.
Definition ExprRef          (p : Syntax.Program) := NodeRefOf p ExpressionKind.
(* a conversion's SOURCE type-name occurrence (C4): a typed reference to a TypeNameKind node — the source
   identity of a conversion target, from which the retained source [Syntax.TypeExpr] spelling is recovered. *)
Definition TypeNameRef      (p : Syntax.Program) := NodeRefOf p TypeNameKind.

Definition syntaxkind_eq_dec (a b : Kind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* the generic kind-refiner: refine a reference to kind [k] iff its source occurrence has kind [k] — the
   kind proof comes from [node_kind_matches_source], so it cannot be forged. *)
Definition as_kind {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) (k : Kind) : option (NodeRefOf p k) :=
  match syntaxkind_eq_dec (Snapshot.node_kind idx r) k with
  | left H  => Some (exist _ r (eq_trans (eq_sym (Snapshot.node_kind_matches_source p idx r)) H))
  | right _ => None
  end.
Definition as_file_node {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (FileNodeRef p) := as_kind idx r FileKind.
Definition as_package_clause {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (PackageClauseRef p) := as_kind idx r PackageClauseKind.
Definition as_decl {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (DeclRef p) := as_kind idx r DeclarationKind.
Definition as_stmt {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (StmtRef p) := as_kind idx r StatementKind.
Definition as_expr {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (ExprRef p) := as_kind idx r ExpressionKind.
Definition as_type_name {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) : option (TypeNameRef p) := as_kind idx r TypeNameKind.

(* refinement soundness: erasure recovers exactly the refined reference. *)
Lemma erase_as_kind {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) (k : Kind) (tr : NodeRefOf p k) :
  as_kind idx r k = Some tr -> erase_ref tr = r.
Proof.
  unfold as_kind. destruct (syntaxkind_eq_dec (Snapshot.node_kind idx r) k); [|discriminate].
  intros H; injection H as <-. reflexivity.
Qed.
(* refinement completeness: a reference whose kind matches refines (and erases back to itself). *)
Lemma as_kind_complete {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) (k : Kind) :
  Snapshot.node_kind idx r = k -> exists tr, as_kind idx r k = Some tr /\ erase_ref tr = r.
Proof.
  intros H. unfold as_kind. destruct (syntaxkind_eq_dec (Snapshot.node_kind idx r) k) as [Heq|Hne]; [|contradiction].
  eexists. split; reflexivity.
Qed.
(* mismatch rejects — no fallback. *)
Lemma as_kind_mismatch {p} (idx : Snapshot.Syntax p) (r : Snapshot.NodeRef p) (k : Kind) :
  Snapshot.node_kind idx r <> k -> as_kind idx r k = None.
Proof.
  intros H. unfold as_kind. destruct (syntaxkind_eq_dec (Snapshot.node_kind idx r) k); [contradiction|reflexivity].
Qed.
(* the refined kind IS the exact source occurrence's kind (tied to the source, not free). *)
Lemma noderefof_kind {p k} (tr : NodeRefOf p k) :
  occurrence_kind (Snapshot.source_occurrence_of_ref (erase_ref tr)) = k.
Proof. destruct tr as [r Hk]. exact Hk. Qed.

(* the SOURCE type-name syntax a [TypeNameRef] designates — the retained source spelling recovered THROUGH the
   reference (never from the resolved semantic fact).  Always [Some] for a real [TypeNameRef] (its occurrence
   is TypeNameKind by construction). *)
Definition type_name_ref_syntax {p} (tr : TypeNameRef p) : option Syntax.TypeExpr :=
  view_typename (Snapshot.source_occurrence_of_ref (erase_ref tr)).
Lemma type_name_ref_syntax_some {p} (tr : TypeNameRef p) :
  exists ts, type_name_ref_syntax tr = Some ts.
Proof. unfold type_name_ref_syntax. apply kind_view_typename, noderefof_kind. Qed.
(* erased Key determines typed-reference identity — no new identity system. *)
Lemma noderefof_key_inj {p k} (tr1 tr2 : NodeRefOf p k) :
  Snapshot.node_ref_key (erase_ref tr1) = Snapshot.node_ref_key (erase_ref tr2) -> tr1 = tr2.
Proof.
  intros H. destruct tr1 as [r1 H1], tr2 as [r2 H2]. cbn [erase_ref proj1_sig] in *.
  assert (r1 = r2) by (apply Snapshot.node_ref_key_inj; exact H). subst r2.
  f_equal. apply (UIP_dec syntaxkind_eq_dec).
Qed.

(** ** snapshot-locality + mutation-sensitive regressions over the REAL grammar.               *)

Definition main_file_path : FilePath.T := FilePath.Make "main.go"%string eq_refl.
Definition ms_gen : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated"%string eq_refl) Version.Go1_23.
Definition ms_com : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/common"%string eq_refl) Version.Go1_23.

(* --- helper: recover a minted reference's exact source occurrence by computing the source spec. --- *)
Lemma soor_compute {p} (r : Snapshot.NodeRef p) (f : Syntax.File) (local : positive) (occ0 : Occurrence) :
  Snapshot.file_ref_source (Snapshot.node_ref_file r) = f -> Snapshot.node_ref_local r = local ->
  source_occurrence_at f local = Some occ0 ->
  Snapshot.source_occurrence_of_ref r = occ0.
Proof.
  intros Hf Hl Hs. pose proof (Snapshot.source_occ_of_ref_eq r) as He.
  rewrite Hf, Hl, Hs in He. injection He as <-. reflexivity.
Qed.

(* ---------- REQUIRED: println(1, 1) — two structurally EQUAL args are DISTINCT occurrences. ---------- *)
(* preorder ids: 1 file / 2 package / 3 decl / 4 stmt / 5 arg0 (Syntax.IntegerLiteral 1) / 6 arg1 (Syntax.IntegerLiteral 1). *)
Definition sf11 : Syntax.File := main_source [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1%N ; Syntax.IntegerLiteral 1%N ] ] ].
Definition prog11 : Syntax.Program := singleton_program ms_gen main_file_path [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1%N ; Syntax.IntegerLiteral 1%N ] ] ].

Lemma find11 : find_file main_file_path (Syntax.files prog11) = Some sf11.
Proof. unfold find_file, prog11, sf11, singleton_program, Syntax.files. apply Collections.FileFacts.add_eq_o. reflexivity. Qed.
(* validity is proved through the source spec: Table is SEALED, so [valid_localb] cannot be computed
   directly; [build_file_source_exact] replaces the opaque [Table.get] with the computable table-free
   [source_occurrence_at]. *)
Ltac valid_via_source := unfold valid_localb; rewrite build_file_source_exact; vm_compute; reflexivity.
Lemma valid11_5 : valid_localb sf11 5%positive = true. Proof. valid_via_source. Qed.
Lemma valid11_6 : valid_localb sf11 6%positive = true. Proof. valid_via_source. Qed.
Lemma src11_5 : source_occurrence_at sf11 5%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 1%N)) (Some 4%positive) (PrintlnArgument 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Lemma src11_6 : source_occurrence_at sf11 6%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 1%N)) (Some 4%positive) (PrintlnArgument 1) 6%positive).
Proof. vm_compute. reflexivity. Qed.

(* the two args, minted as validated ExprRefs through the sealed key-minting boundary. *)
Theorem regression_println_1_1 :
  exists (r5 r6 : Snapshot.NodeRef prog11),
    Snapshot.ref_of_key prog11 (Snapshot.index_program prog11) (MakeKey main_file_path 5%positive) = Some r5 /\
    Snapshot.ref_of_key prog11 (Snapshot.index_program prog11) (MakeKey main_file_path 6%positive) = Some r6 /\
    (* both source fragments are EQUAL... *)
    Snapshot.node_at r5 = Some (Syntax.IntegerLiteral 1%N) /\ Snapshot.node_at r6 = Some (Syntax.IntegerLiteral 1%N) /\
    (* ...yet the two references are DISTINCT (distinct keys / local ids), NOT deduplicated... *)
    r5 <> r6 /\
    Snapshot.node_ref_key r5 = MakeKey main_file_path 5%positive /\ Snapshot.node_ref_key r6 = MakeKey main_file_path 6%positive /\
    (* ...with the correct per-argument role. *)
    Snapshot.node_role (Snapshot.index_program prog11) r5 = PrintlnArgument 0 /\
    Snapshot.node_role (Snapshot.index_program prog11) r6 = PrintlnArgument 1.
Proof.
  destruct (Snapshot.ref_of_key_source prog11 (Snapshot.index_program prog11) main_file_path sf11 5%positive find11 valid11_5)
    as [r5 [Hk5 [Hl5 Hf5]]].
  destruct (Snapshot.ref_of_key_source prog11 (Snapshot.index_program prog11) main_file_path sf11 6%positive find11 valid11_6)
    as [r6 [Hk6 [Hl6 Hf6]]].
  pose proof (soor_compute r5 sf11 5%positive _ Hf5 Hl5 src11_5) as Ho5.
  pose proof (soor_compute r6 sf11 6%positive _ Hf6 Hl6 src11_6) as Ho6.
  pose proof (Snapshot.ref_of_key_sound prog11 (Snapshot.index_program prog11) (MakeKey main_file_path 5%positive) r5 Hk5) as Hkey5.
  pose proof (Snapshot.ref_of_key_sound prog11 (Snapshot.index_program prog11) (MakeKey main_file_path 6%positive) r6 Hk6) as Hkey6.
  exists r5, r6. repeat split; try assumption.
  - rewrite (Snapshot.node_at_matches_source_view r5), Ho5. reflexivity.
  - rewrite (Snapshot.node_at_matches_source_view r6), Ho6. reflexivity.
  - intro Hbad. rewrite Hbad, Hkey6 in Hkey5. injection Hkey5 as Hkey5. discriminate Hkey5.
  - rewrite (Snapshot.node_role_matches_source prog11 (Snapshot.index_program prog11) r5), Ho5. reflexivity.
  - rewrite (Snapshot.node_role_matches_source prog11 (Snapshot.index_program prog11) r6), Ho6. reflexivity.
Qed.

(* ---------- same path + shape, DIFFERENT payload => non-interchangeable ref TYPES + per-snapshot
   payload recovery; erased index DATA is extensionally equal (metadata discards the payload). ---------- *)
Definition program_a : Syntax.Program := singleton_program ms_gen main_file_path [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 5%N ] ] ].
Definition program_b : Syntax.Program := singleton_program ms_gen main_file_path [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 6%N ] ] ].
Definition sf_a : Syntax.File := main_source [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 5%N ] ] ].
Definition sf_b : Syntax.File := main_source [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 6%N ] ] ].

Lemma find_a : find_file main_file_path (Syntax.files program_a) = Some sf_a.
Proof. unfold find_file, program_a, sf_a, singleton_program, Syntax.files. apply Collections.FileFacts.add_eq_o. reflexivity. Qed.
Lemma find_b : find_file main_file_path (Syntax.files program_b) = Some sf_b.
Proof. unfold find_file, program_b, sf_b, singleton_program, Syntax.files. apply Collections.FileFacts.add_eq_o. reflexivity. Qed.
Lemma valid_a5 : valid_localb sf_a 5%positive = true. Proof. valid_via_source. Qed.
Lemma valid_b5 : valid_localb sf_b 5%positive = true. Proof. valid_via_source. Qed.
Lemma src_a5 : source_occurrence_at sf_a 5%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 5%N)) (Some 4%positive) (PrintlnArgument 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Lemma src_b5 : source_occurrence_at sf_b 5%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 6%N)) (Some 4%positive) (PrintlnArgument 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.

(* the SAME Key recovers each snapshot's OWN payload: Syntax.IntegerLiteral 5 in program_a, Syntax.IntegerLiteral 6 in program_b. *)
Theorem regression_payload_a : exists r, Snapshot.ref_of_key program_a (Snapshot.index_program program_a) (MakeKey main_file_path 5%positive) = Some r
                                  /\ Snapshot.node_at r = Some (Syntax.IntegerLiteral 5%N).
Proof.
  destruct (Snapshot.ref_of_key_source program_a (Snapshot.index_program program_a) main_file_path sf_a 5%positive find_a valid_a5)
    as [r [Hk [Hl Hf]]].
  exists r. split; [exact Hk|].
  rewrite (Snapshot.node_at_matches_source_view r), (soor_compute r sf_a 5%positive _ Hf Hl src_a5). reflexivity.
Qed.
Theorem regression_payload_b : exists r, Snapshot.ref_of_key program_b (Snapshot.index_program program_b) (MakeKey main_file_path 5%positive) = Some r
                                  /\ Snapshot.node_at r = Some (Syntax.IntegerLiteral 6%N).
Proof.
  destruct (Snapshot.ref_of_key_source program_b (Snapshot.index_program program_b) main_file_path sf_b 5%positive find_b valid_b5)
    as [r [Hk [Hl Hf]]].
  exists r. split; [exact Hk|].
  rewrite (Snapshot.node_at_matches_source_view r), (soor_compute r sf_b 5%positive _ Hf Hl src_b5). reflexivity.
Qed.

(* non-interchangeability at the TYPE level: a reference of [program_a] is NOT a reference of [program_b]. *)
Fail Definition reg_cross_snapshot (r : Snapshot.NodeRef program_a) : Snapshot.NodeRef program_b := r.

(* the ERASED index data is extensionally equal — the metadata builder discards the leaf payload (5 vs 6),
   so [outer_of] of the two snapshots are [FileMap.Equal]; only the [Syntax.Program] distinguishes the ref TYPES. *)
Theorem regression_index_data_equal : FileMap.Equal (outer_of (Syntax.files program_a)) (outer_of (Syntax.files program_b)).
Proof.
  intro k. unfold outer_of, program_a, program_b, singleton_program, Syntax.files.
  rewrite !FileFacts.map_o, !FileFacts.add_o.
  destruct (Collections.FilePathOrder.eq_dec main_file_path k) as [Heq|Hne].
  - cbn [option_map]. reflexivity.
  - rewrite !FileFacts.empty_o. reflexivity.
Qed.

(* ---------- same FILE MAP, DIFFERENT ModuleSpec => non-interchangeable ref TYPES even though the
   erased index data is IDENTICAL: references are indexed by the exact [Syntax.Program], not by index data. ---------- *)
Definition program_generated : Syntax.Program := singleton_program ms_gen main_file_path [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 5%N ] ] ].
Definition program_common : Syntax.Program := singleton_program ms_com main_file_path [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 5%N ] ] ].
(* their file maps are identical, hence their outer index maps are equal... *)
Theorem regression_module_index_equal : FileMap.Equal (outer_of (Syntax.files program_generated)) (outer_of (Syntax.files program_common)).
Proof. intro k. reflexivity. Qed.
(* ...yet a reference of one is NOT a reference of the other (distinct Syntax.Program snapshots). *)
Fail Definition reg_cross_module (r : Snapshot.NodeRef program_generated) : Snapshot.NodeRef program_common := r.

(* ---------- a compact, structurally rich mutation-sensitive fixture.  Preorder ids 1..13:
   1 file / 2 package / 3 decl0 / 4 stmt0 / 5 arg0 (Syntax.IntegerLiteral 1) / 6 arg1 (Syntax.IntegerLiteral 1) / 7 stmt1 / 8 arg (Syntax.BoolLiteral true)
   / 9 decl1 / 10 stmt0 / 11 arg0 = outer conversion / 12 inner conversion operand / 13 leaf (Syntax.IntegerLiteral 5).
   Each stored metadatum is derived from the UNIVERSAL exactness theorem (rewrite by build_file_source_exact,
   then compute the INDEPENDENT source spec) — NEVER by unfolding the builder.  A wrong builder kind / role /
   parent / index / subtree makes [build_file_source_exact] unprovable, so these pin exact per-occurrence
   labels; the repeated Syntax.IntegerLiteral 1 args (ids 5,6) are NOT collapsed, and the nested conversion chain (ids 11..15)
   pins the ConversionTarget / ConversionOperand two-child relationship. ---------- *)
Definition wf : Syntax.File := main_source
  [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1%N ; Syntax.IntegerLiteral 1%N ] ; Syntax.Println [ Syntax.BoolLiteral true ] ]
  ; Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5%N)) ] ] ].

Ltac wf_meta := rewrite build_file_source_exact; vm_compute; reflexivity.
Example well_formed_meta_file  : Table.get 1%positive  (table (build_file wf)) = Some (MakeMeta FileKind         None      FileRoot        15). Proof. wf_meta. Qed.
Example well_formed_meta_pkg   : Table.get 2%positive  (table (build_file wf)) = Some (MakeMeta PackageClauseKind (Some 1)  FilePackage      2). Proof. wf_meta. Qed.
Example well_formed_meta_decl0 : Table.get 3%positive  (table (build_file wf)) = Some (MakeMeta DeclarationKind  (Some 1)  (FileDeclaration 0)     8). Proof. wf_meta. Qed.
Example well_formed_meta_stmt0 : Table.get 4%positive  (table (build_file wf)) = Some (MakeMeta StatementKind     (Some 3)  (DeclarationStatement 0)     6). Proof. wf_meta. Qed.
Example well_formed_meta_arg0  : Table.get 5%positive  (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 4)  (PrintlnArgument 0)   5). Proof. wf_meta. Qed.
Example well_formed_meta_arg1  : Table.get 6%positive  (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 4)  (PrintlnArgument 1)   6). Proof. wf_meta. Qed.
Example well_formed_meta_stmt1 : Table.get 7%positive  (table (build_file wf)) = Some (MakeMeta StatementKind     (Some 3)  (DeclarationStatement 1)     8). Proof. wf_meta. Qed.
Example well_formed_meta_bool  : Table.get 8%positive  (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 7)  (PrintlnArgument 0)   8). Proof. wf_meta. Qed.
Example well_formed_meta_decl1 : Table.get 9%positive  (table (build_file wf)) = Some (MakeMeta DeclarationKind  (Some 1)  (FileDeclaration 1)    15). Proof. wf_meta. Qed.
Example well_formed_meta_stmt2 : Table.get 10%positive (table (build_file wf)) = Some (MakeMeta StatementKind     (Some 9)  (DeclarationStatement 0)    15). Proof. wf_meta. Qed.
Example well_formed_meta_conv0  : Table.get 11%positive (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 10) (PrintlnArgument 0)     15). Proof. wf_meta. Qed.
Example well_formed_meta_tname0 : Table.get 12%positive (table (build_file wf)) = Some (MakeMeta TypeNameKind      (Some 11) ConversionTarget  12). Proof. wf_meta. Qed.
Example well_formed_meta_conv1  : Table.get 13%positive (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 11) ConversionOperand 15). Proof. wf_meta. Qed.
Example well_formed_meta_tname1 : Table.get 14%positive (table (build_file wf)) = Some (MakeMeta TypeNameKind      (Some 13) ConversionTarget  14). Proof. wf_meta. Qed.
Example well_formed_meta_leaf   : Table.get 15%positive (table (build_file wf)) = Some (MakeMeta ExpressionKind    (Some 13) ConversionOperand 15). Proof. wf_meta. Qed.
Example well_formed_meta_absent : Table.get 16%positive (table (build_file wf)) = None. Proof. wf_meta. Qed.

(* source-VIEW recovery: the INDEPENDENT spec recovers the exact original fragment (the [occurrence_view] that
   [occurrence_meta] erases) for each occurrence kind — package clause / an argument / the innermost leaf. *)
Example well_formed_view_pkg  : source_occurrence_at wf 2%positive
  = Some (MakeOccurrence PackageClauseKind (PackageClauseView Syntax.MainPackage) (Some 1%positive) FilePackage 2%positive).
Proof. vm_compute. reflexivity. Qed.
Example well_formed_view_arg0 : source_occurrence_at wf 5%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 1%N)) (Some 4%positive) (PrintlnArgument 0) 5%positive).
Proof. vm_compute. reflexivity. Qed.
Example well_formed_view_leaf : source_occurrence_at wf 15%positive
  = Some (MakeOccurrence ExpressionKind (ExpressionView (Syntax.IntegerLiteral 5%N)) (Some 13%positive) ConversionOperand 15%positive).
Proof. vm_compute. reflexivity. Qed.
Example well_formed_view_tname0 : source_occurrence_at wf 12%positive
  = Some (MakeOccurrence TypeNameKind (TypeNameView (Syntax.type_expr_of_name Names.Int)) (Some 11%positive) ConversionTarget 12%positive).
Proof. vm_compute. reflexivity. Qed.

(* the retained Program phase boundary.

   ONE immutable [Syntax.Program] elaborates EXACTLY ONCE into one retained structural index.  The exact program is
   the TYPE PARAMETER (no second source copy, no equality transport); the one retained [Snapshot.Syntax p] is
   the sole field.  Every downstream query works through [indexed_syntax]; nothing reconstructs
   [Snapshot.index_program p].  Semantic-free, axiom-free. *)

Record Program (p : Syntax.Program) : Type := MakeProgram { index : Snapshot.Syntax p }.
Arguments MakeProgram {p} _.
Arguments index {p} _.

Definition index_program (p : Syntax.Program) : Program p := MakeProgram (Snapshot.index_program p).

Definition indexed_syntax {p} (ip : Program p) : Snapshot.Syntax p := index ip.

(* [index_program] uses EXACTLY [Snapshot.index_program p] (one canonical elaboration), and the retained index is
   the projected field — no query rebuilds the per-program index. *)
Lemma index_program_syntax : forall p, indexed_syntax (index_program p) = Snapshot.index_program p.
Proof. reflexivity. Qed.

Lemma indexed_syntax_proj : forall p (ip : Program p), indexed_syntax ip = index ip.
Proof. reflexivity. Qed.

(* the canonical occurrence-identity ordered key + its standard AVL map.

   [Key] = FilePath.T + local positive id.  Its total order is LEXICOGRAPHIC: the [FilePath.T] order first, the
   local positive id second — the permanent source-occurrence order used by fact enumeration, node-diagnostic
   enumeration, and deterministic reports.  Storage delegates ENTIRELY to the pinned-stdlib [FMapAVL]; Fido
   authors no map. *)

Module KeyOrderedType <: OrderedType.OrderedType.
  Definition t := Key.
  Definition eq (a b : t) := a = b.
  Definition lt (a b : t) :=
    Collections.FilePathOrder.lt (key_path a) (key_path b) \/
    (key_path a = key_path b /\ (key_local a < key_local b)%positive).
  Lemma eq_refl : forall x, eq x x. Proof. reflexivity. Qed.
  Lemma eq_sym : forall x y, eq x y -> eq y x. Proof. unfold eq; intros x y H; symmetry; exact H. Qed.
  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; intros x y z Hxy Hyz; rewrite Hxy; exact Hyz. Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z [H1|[H1 H1']] [H2|[H2 H2']].
    - left. eapply Collections.FilePathOrder.lt_trans; eauto.
    - left. rewrite <- H2. exact H1.
    - left. rewrite H1. exact H2.
    - right. split; [ rewrite H1; exact H2 | eapply Pos.lt_trans; eauto ].
  Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros x y [H|[H H']] Heq; subst y.
    - apply (Collections.FilePathOrder.lt_not_eq H); reflexivity.
    - eapply Pos.lt_irrefl; exact H'.
  Qed.
  Definition compare (a b : t) : OrderedType.Compare lt eq a b.
  Proof.
    destruct (Collections.FilePathOrder.compare (key_path a) (key_path b)) as [Hlt|Heq|Hgt].
    - apply OrderedType.LT. left. exact Hlt.
    - unfold Collections.FilePathOrder.eq in Heq.
      destruct (key_local a ?= key_local b)%positive eqn:E.
      + apply OrderedType.EQ. apply Pos.compare_eq in E. unfold eq.
        destruct a as [fa la], b as [fb lb]; cbn in *; subst; reflexivity.
      + apply OrderedType.LT. right. split; [ exact Heq | apply Pos.compare_lt_iff in E; exact E ].
      + apply OrderedType.GT. right. split; [ symmetry; exact Heq | apply Pos.compare_gt_iff in E; exact E ].
    - apply OrderedType.GT. left. exact Hgt.
  Defined.
  Definition eq_dec (a b : t) : {eq a b} + {~ eq a b}.
  Proof. unfold eq. apply key_eq_dec. Defined.
End KeyOrderedType.

Module KeyMap  := FMapAVL.Make KeyOrderedType.
Module KeyFacts := FMapFacts.WFacts_fun KeyOrderedType KeyMap.
Module KeyProperties := FMapFacts.WProperties_fun KeyOrderedType KeyMap.
Module KeyOrder   := FMapFacts.OrdProperties KeyMap.

(* the ordered-key laws Fido depends on (all delegate to the standard map). *)
Lemma key_compare_equal : forall a b, KeyOrderedType.eq a b <-> a = b.
Proof. reflexivity. Qed.

Lemma key_map_add_equal {A} : forall (m : KeyMap.t A) k v,
  KeyMap.find k (KeyMap.add k v m) = Some v.
Proof. intros; apply KeyFacts.add_eq_o; reflexivity. Qed.

Lemma key_map_add_unequal {A} : forall (m : KeyMap.t A) k k' v,
  k <> k' -> KeyMap.find k' (KeyMap.add k v m) = KeyMap.find k' m.
Proof. intros m k k' v Hne; apply KeyFacts.add_neq_o; intro H; apply Hne; exact H. Qed.

(* canonical elements: key-sorted, and a FUNCTION of the map's meaning ([Equal] maps have equal [elements]) —
   the permanent basis for deterministic fact/diagnostic enumeration.  (Key equality is Leibniz, so
   [eqlistA eq_key_elt] collapses to list equality.) *)
Lemma key_equal_list_key_element_equal {A} : forall (l1 l2 : list (Key * A)),
  eqlistA (@KeyMap.eq_key_elt A) l1 l2 -> l1 = l2.
Proof.
  induction l1 as [|[k e] l1' IH]; intros l2 H; inversion H as [|x y l l' Hxy Htl]; subst; [ reflexivity | ].
  destruct y as [k' e']. destruct Hxy as [Hk He]. cbn in Hk, He.
  unfold KeyOrderedType.eq in Hk. subst. f_equal. apply IH; exact Htl.
Qed.

Lemma key_map_elements_equal {A} : forall (m1 m2 : KeyMap.t A),
  KeyMap.Equal m1 m2 -> KeyMap.elements m1 = KeyMap.elements m2.
Proof.
  intros m1 m2 Heq. apply key_equal_list_key_element_equal.
  apply KeyOrder.sort_equivlistA_eqlistA;
    [ apply KeyMap.elements_3 | apply KeyMap.elements_3 | ].
  intros [k e]. rewrite <- !KeyFacts.elements_mapsto_iff, !KeyFacts.find_mapsto_iff, (Heq k).
  reflexivity.
Qed.
