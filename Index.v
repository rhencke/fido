
From Stdlib Require Import PArith NArith List Bool Lia Sorted Recdef Wf_nat Arith Eqdep_dec String.
From Stdlib Require Import Structures.OrderedType FSets.FMapAVL FSets.FMapFacts SetoidList.
From Fido Require Import FilePath Collections Syntax.
Import ListNotations.
Local Open Scope positive_scope.

(* The node table's abstract interface; the sealing hides the standard map's operations, not its choice. *)

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

(* The occurrence universe; no kind exists ahead of the syntax it would designate. *)
Inductive Kind :=
| FileKind | PackageClauseKind
| TopLevelKind | DeclarationKind | SpecKind | BindingNameKind | TypeNameKind
| StatementKind | BlockKind | ExpressionKind.

(* how an occurrence participates in its parent, in source order *)
Inductive Role :=
| FileRoot
| FilePackage
| FileDeclaration (n : nat)
| MainBlock
| BlockStatement (n : nat)
| ExprStatementExpr
| DeclStatementDecl
| ShortLhs (n : nat)
| ShortRhs (n : nat)
| DeclSpec (n : nat)
| SpecName (n : nat)
| SpecTypeUse
| SpecValue (n : nat)
| UnaryOperand
| ApplicationHead
| ApplicationArgument (n : nat).

(* small structural metadata, with no copy of the recursive subtree *)
Record Meta := MakeMeta {
  kind        : Kind;
  parent      : option positive;
  role        : Role;
  subtree_end : positive
}.

Definition root_id : positive := 1.
Definition package_id  : positive := 2.

(* total extraction from a provably-present option, the basis for the total reference API *)
Definition option_get {A} (o : option A) : o <> None -> A :=
  match o with Some a => fun _ => a | None => fun H => False_rect A (H eq_refl) end.
Lemma option_get_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> option_get o H = a.
Proof. intros Heq. subst o. reflexivity. Qed.
Lemma option_get_some {A} (o : option A) : forall (H : o <> None), o = Some (option_get o H).
Proof. destruct o as [a|]; intro H; [reflexivity | exfalso; exact (H eq_refl)]. Qed.

(* the import list is intrinsically nil, and consuming it structurally makes a future constructor break here *)
Lemma import_list_nil : forall (l : list Syntax.ImportSpec), l = [].
Proof. intros [|i rest]; [ reflexivity | destruct i ]. Qed.

(* the three spec shapes share one occurrence kind; this is the retained spec payload *)
Inductive AnySpec : Type :=
| ASConst : Syntax.ConstSpec -> AnySpec
| ASVar   : Syntax.VarSpec  -> AnySpec
| ASType  : Syntax.TypeSpec -> AnySpec.

Inductive View : Kind -> Type :=
| FileView          : Syntax.File         -> View FileKind
| PackageClauseView : Syntax.PackageClause -> View PackageClauseKind
| TopLevelView      : Syntax.TopLevelDecl -> View TopLevelKind
| DeclarationView   : Syntax.Declaration  -> View DeclarationKind
| SpecView          : AnySpec             -> View SpecKind
| BindingNameView   : Syntax.BindingName  -> View BindingNameKind
| TypeNameView      : Syntax.TypeExpr     -> View TypeNameKind
| StatementView     : Syntax.Stmt         -> View StatementKind
| BlockView         : Syntax.Block        -> View BlockKind
| ExpressionView    : Syntax.Expr         -> View ExpressionKind.

Record Occurrence := MakeOccurrence {
  occurrence_kind        : Kind;
  occurrence_view        : View occurrence_kind;
  occurrence_parent      : option positive;
  occurrence_role        : Role;
  occurrence_subtree_end : positive
}.

Definition occurrence_meta (o : Occurrence) : Meta :=
  MakeMeta (occurrence_kind o) (occurrence_parent o) (occurrence_role o) (occurrence_subtree_end o).

Definition view_expr (o : Occurrence) : option Syntax.Expr :=
  match occurrence_view o with ExpressionView e => Some e | _ => None end.

(* [view_expr] is [Some] EXACTLY for an [ExpressionKind] occurrence (the dependent [View] forces the kind). *)
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
          | FileView _ => I | PackageClauseView _ => I | TopLevelView _ => I | DeclarationView _ => I
          | SpecView _ => I | BindingNameView _ => I | TypeNameView _ => I | StatementView _ => I | BlockView _ => I
          end).
Qed.

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
          | FileView _ => I | PackageClauseView _ => I | TopLevelView _ => I | DeclarationView _ => I
          | SpecView _ => I | BindingNameView _ => I | ExpressionView _ => I | StatementView _ => I | BlockView _ => I
          end).
Qed.

Definition view_binding_name (o : Occurrence) : option Syntax.BindingName :=
  match occurrence_view o with BindingNameView b => Some b | _ => None end.
Lemma view_binding_name_kind : forall o b, view_binding_name o = Some b -> occurrence_kind o = BindingNameKind.
Proof.
  intros [k v par role sub] b H. cbn [view_binding_name occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

Definition view_toplevel (o : Occurrence) : option Syntax.TopLevelDecl :=
  match occurrence_view o with TopLevelView d => Some d | _ => None end.
Lemma view_toplevel_kind : forall o d, view_toplevel o = Some d -> occurrence_kind o = TopLevelKind.
Proof.
  intros [k v par role sub] d H. cbn [view_toplevel occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

Definition view_stmt (o : Occurrence) : option Syntax.Stmt :=
  match occurrence_view o with StatementView s => Some s | _ => None end.
Lemma view_stmt_kind : forall o s, view_stmt o = Some s -> occurrence_kind o = StatementKind.
Proof.
  intros [k v par role sub] s H. cbn [view_stmt occurrence_view occurrence_kind] in *.
  destruct v; try discriminate H. reflexivity.
Qed.

(* One-pass occurrence fold: each node yields its member before its children, so the list is in ascending id order. *)
Fixpoint occ_expr (parent : positive) (role : Role) (me : positive) (e : Syntax.Expr)
  : list (positive * Occurrence) * positive :=
  match e with
  | Syntax.Name _ | Syntax.LiteralExpr _ =>
      ([(me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role me)], me)
  | Syntax.Unary _ e' =>
      let '(os, e1) := occ_expr me UnaryOperand (Pos.succ me) e' in
      ((me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role e1) :: os, e1)
  | Syntax.Application head args =>
      let '(oh, eh) := occ_expr me ApplicationHead (Pos.succ me) head in
      let '(oa, nx) := (fix oa (i : nat) (mi : positive) (xs : list Syntax.Expr)
                          : list (positive * Occurrence) * positive :=
                          match xs with
                          | []        => ([], mi)
                          | x :: rest =>
                              let '(o1, se) := occ_expr me (ApplicationArgument i) mi x in
                              let '(o2, r)  := oa (S i) (Pos.succ se) rest in
                              (o1 ++ o2, r)
                          end) 0%nat (Pos.succ eh) args in
      ((me, MakeOccurrence ExpressionKind (ExpressionView e) (Some parent) role (Pos.pred nx)) :: oh ++ oa, Pos.pred nx)
  end.

Fixpoint occ_seq {X}
  (ox : positive -> nat -> positive -> X -> list (positive * Occurrence) * positive)
  (parent : positive) (i0 : nat) (me0 : positive) (xs : list X)
  : list (positive * Occurrence) * positive :=
  match xs with
  | []        => ([], me0)
  | x :: rest =>
      let '(o1, se) := ox parent i0 me0 x in
      let '(o2, nf) := occ_seq ox parent (S i0) (Pos.succ se) rest in
      (o1 ++ o2, nf)
  end.

Definition occ_type_expr (parent : positive) (role : Role) (me : positive) (ty : Syntax.TypeExpr)
  : list (positive * Occurrence) * positive :=
  ([(me, MakeOccurrence TypeNameKind (TypeNameView ty) (Some parent) role me)], me).
Definition occ_binding_name (parent : positive) (role : Role) (me : positive) (b : Syntax.BindingName)
  : list (positive * Occurrence) * positive :=
  ([(me, MakeOccurrence BindingNameKind (BindingNameView b) (Some parent) role me)], me).

Definition occ_opt_type (parent : positive) (me : positive) (oty : option Syntax.TypeExpr)
  : list (positive * Occurrence) * positive :=
  match oty with
  | Some ty => let '(o1, e1) := occ_type_expr parent SpecTypeUse me ty in (o1, Pos.succ e1)
  | None    => ([], me)
  end.

Definition occ_names (parent : positive) (me : positive) (ns : Collections.NonEmpty Syntax.BindingName)
  : list (positive * Occurrence) * positive :=
  occ_seq (fun p i m x => occ_binding_name p (SpecName i) m x) parent 0 me (Collections.ne_to_list ns).
Definition occ_values (parent : positive) (me : positive) (vs : Collections.NonEmpty Syntax.Expr)
  : list (positive * Occurrence) * positive :=
  occ_seq (fun p i m x => occ_expr p (SpecValue i) m x) parent 0 me (Collections.ne_to_list vs).

Definition occ_const_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.ConstSpec)
  : list (positive * Occurrence) * positive :=
  let '(on, m1) := occ_names me (Pos.succ me) (Syntax.const_names s) in
  let '(ov, nx) :=
    match Syntax.const_init s with
    | Syntax.ExplicitConstInit oty vals =>
        let '(o1, m2) := occ_opt_type me m1 oty in let '(o2, r) := occ_values me m2 vals in (o1 ++ o2, r)
    | Syntax.InheritedConstInit => ([], m1)
    end in
  ((me, MakeOccurrence SpecKind (SpecView (ASConst s)) (Some parent) (DeclSpec didx) (Pos.pred nx)) :: on ++ ov, Pos.pred nx).

Definition occ_var_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.VarSpec)
  : list (positive * Occurrence) * positive :=
  let '(on, m1) := occ_names me (Pos.succ me) (Syntax.var_names s) in
  let '(ov, nx) :=
    match Syntax.var_init s with
    | Syntax.VarTypeOnly ty => occ_opt_type me m1 (Some ty)
    | Syntax.VarValues oty vals =>
        let '(o1, m2) := occ_opt_type me m1 oty in let '(o2, r) := occ_values me m2 vals in (o1 ++ o2, r)
    end in
  ((me, MakeOccurrence SpecKind (SpecView (ASVar s)) (Some parent) (DeclSpec didx) (Pos.pred nx)) :: on ++ ov, Pos.pred nx).

Definition occ_type_spec (parent : positive) (didx : nat) (me : positive) (s : Syntax.TypeSpec)
  : list (positive * Occurrence) * positive :=
  let '(on, target) := match s with Syntax.AliasSpec nm ty | Syntax.DefSpec nm ty =>
    let '(o1, e1) := occ_binding_name me (SpecName 0) (Pos.succ me) nm in
    let '(o2, e2) := occ_type_expr me SpecTypeUse (Pos.succ e1) ty in (o1 ++ o2, e2) end in
  ((me, MakeOccurrence SpecKind (SpecView (ASType s)) (Some parent) (DeclSpec didx) target) :: on, target).

Definition occ_declaration (parent : positive) (role : Role) (me : positive) (d : Syntax.Declaration)
  : list (positive * Occurrence) * positive :=
  let '(od, nx) :=
    match d with
    | Syntax.ConstDecl specs => occ_seq occ_const_spec me 0 (Pos.succ me) specs
    | Syntax.VarDecl specs   => occ_seq occ_var_spec me 0 (Pos.succ me) specs
    | Syntax.TypeDecl specs  => occ_seq occ_type_spec me 0 (Pos.succ me) specs
    end in
  ((me, MakeOccurrence DeclarationKind (DeclarationView d) (Some parent) role (Pos.pred nx)) :: od, Pos.pred nx).

Definition occ_stmt (parent : positive) (sidx : nat) (me : positive) (s : Syntax.Stmt)
  : list (positive * Occurrence) * positive :=
  match s with
  | Syntax.ExprStmt e =>
      let '(o1, e1) := occ_expr me ExprStatementExpr (Pos.succ me) e in
      ((me, MakeOccurrence StatementKind (StatementView s) (Some parent) (BlockStatement sidx) e1) :: o1, e1)
  | Syntax.DeclarationStmt d =>
      let '(o1, e1) := occ_declaration me DeclStatementDecl (Pos.succ me) d in
      ((me, MakeOccurrence StatementKind (StatementView s) (Some parent) (BlockStatement sidx) e1) :: o1, e1)
  | Syntax.ShortVarDecl names vals =>
      let '(on, m1) := occ_seq (fun p i m x => occ_binding_name p (ShortLhs i) m x) me 0 (Pos.succ me) (Collections.ne_to_list names) in
      let '(ov, nx) := occ_seq (fun p i m x => occ_expr p (ShortRhs i) m x) me 0 m1 (Collections.ne_to_list vals) in
      ((me, MakeOccurrence StatementKind (StatementView s) (Some parent) (BlockStatement sidx) (Pos.pred nx)) :: on ++ ov, Pos.pred nx)
  end.

Definition occ_block (parent : positive) (role : Role) (me : positive) (b : Syntax.Block)
  : list (positive * Occurrence) * positive :=
  match b with
  | Syntax.MakeBlock stmts =>
      let '(o1, nx) := occ_seq occ_stmt me 0 (Pos.succ me) stmts in
      ((me, MakeOccurrence BlockKind (BlockView b) (Some parent) role (Pos.pred nx)) :: o1, Pos.pred nx)
  end.

Definition occ_decl (parent : positive) (didx : nat) (me : positive) (d : Syntax.TopLevelDecl)
  : list (positive * Occurrence) * positive :=
  match d with
  | Syntax.TopDeclaration dcl =>
      let '(o1, e1) := occ_declaration me (FileDeclaration didx) (Pos.succ me) dcl in
      ((me, MakeOccurrence TopLevelKind (TopLevelView d) (Some parent) (FileDeclaration didx) e1) :: o1, e1)
  | Syntax.Main body =>
      let '(o1, e1) := occ_block me MainBlock (Pos.succ me) body in
      ((me, MakeOccurrence TopLevelKind (TopLevelView d) (Some parent) (FileDeclaration didx) e1) :: o1, e1)
  end.

Definition occ_file (f : Syntax.File) : list (positive * Occurrence) :=
  match Syntax.imports f with
  | i :: _ => match i with end
  | [] =>
      let '(ds, nx) := occ_seq occ_decl root_id 0 (Pos.succ package_id) (Syntax.declarations f) in
      (root_id, MakeOccurrence FileKind (FileView f) None FileRoot (Pos.pred nx))
      :: (package_id, MakeOccurrence PackageClauseKind (PackageClauseView (Syntax.package f)) (Some root_id) FilePackage package_id)
      :: ds
  end.

(* The retained per-file result: the fold's members, and a cheap viewless Meta index derived from them. *)
Record File := MakeFile { file_members : list (positive * Occurrence) ; file_metas : Table.table Meta }.
Definition occ_meta_table (os : list (positive * Occurrence)) : Table.table Meta :=
  fold_left (fun t io => Table.set (fst io) (occurrence_meta (snd io)) t) os Table.empty.
Definition index_file (f : Syntax.File) : File := let os := occ_file f in MakeFile os (occ_meta_table os).

(* the ordered occurrence enumeration for a file is exactly the retained fold — one authority *)
Definition occurrences_file (f : Syntax.File) : list (positive * Occurrence) := occ_file f.

(* A program-global occurrence identity: the file path and the file-local id. *)
Lemma file_path_eq_dec (a b : FilePath.T) : {a = b} + {a <> b}.
Proof.
  destruct (FilePath.equalb a b) eqn:E; [left; apply FilePath.equalb_spec; exact E|].
  right; intro Heq; subst; rewrite (proj2 (FilePath.equalb_spec b b) eq_refl) in E; discriminate.
Qed.

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

(* the retained program-indexed metadata object: one single-pass per-file table, built once from the program *)
Record ProgramIndex (p : Syntax.Program) : Type := MakeIndex {
  idx_files : Collections.FileMap.t File ;
  idx_built : idx_files = Collections.FileMap.map index_file (Syntax.files p)
}.
Arguments MakeIndex {p}. Arguments idx_files {p}. Arguments idx_built {p}.

Definition index_program (p : Syntax.Program) : ProgramIndex p :=
  MakeIndex (Collections.FileMap.map index_file (Syntax.files p)) eq_refl.

(* a metadata query is a lookup in the retained derived Meta index, never a fresh source traversal *)
Definition meta_of {p} (idx : ProgramIndex p) (path : FilePath.T) (local : positive) : option Meta :=
  match Collections.FileMap.find path (idx_files idx) with Some fl => Table.get local (file_metas fl) | None => None end.

(* the retained members for a file, and the exact retained member at a local id — the one occurrence authority *)
Definition members_of {p} (idx : ProgramIndex p) (path : FilePath.T) : list (positive * Occurrence) :=
  match Collections.FileMap.find path (idx_files idx) with Some fl => file_members fl | None => [] end.
Definition member_of {p} (idx : ProgramIndex p) (path : FilePath.T) (local : positive) : option Occurrence :=
  option_map snd (find (fun io => Pos.eqb (fst io) local) (members_of idx path)).

Definition occ_ofb {p} (idx : ProgramIndex p) (path : FilePath.T) (local : positive) : bool :=
  match meta_of idx path local with Some _ => true | None => false end.

Lemma occ_ofb_some : forall p (idx : ProgramIndex p) path local,
  occ_ofb idx path local = true -> meta_of idx path local <> None.
Proof. intros p idx path local H. unfold occ_ofb in H. destruct (meta_of idx path local); [discriminate | discriminate H]. Qed.

Module Snapshot.

(* A file handle: a path with a boolean membership proof; its source is read from the program map. *)
Record FileRef (p : Syntax.Program) : Type := MakeFileRef {
  fr_path : FilePath.T;
  fr_memb : Syntax.file_mem fr_path (Syntax.files p) = true
}.
Arguments MakeFileRef {p}. Arguments fr_path {p}. Arguments fr_memb {p}.

Lemma file_mem_find_some : forall fp (fm : Syntax.Files),
  Syntax.file_mem fp fm = true -> Syntax.find_file fp fm <> None.
Proof.
  intros fp fm H. unfold Syntax.find_file.
  apply Collections.FileFacts.in_find_iff. apply Collections.FileFacts.mem_in_iff. exact H.
Qed.

Definition fr_source {p} (fr : FileRef p) : Syntax.File :=
  option_get (Syntax.find_file (fr_path fr) (Syntax.files p)) (file_mem_find_some _ _ (fr_memb fr)).

Definition file_ref_path {p} (fr : FileRef p) : FilePath.T := fr_path fr.
Definition file_ref_source {p} (fr : FileRef p) : Syntax.File := fr_source fr.

Lemma file_ref_find {p} (fr : FileRef p) :
  Syntax.find_file (fr_path fr) (Syntax.files p) = Some (fr_source fr).
Proof. unfold fr_source. apply option_get_some. Qed.

Lemma file_ref_ext {p} (fr1 fr2 : FileRef p) : fr_path fr1 = fr_path fr2 -> fr1 = fr2.
Proof.
  destruct fr1 as [p1 m1], fr2 as [p2 m2]; cbn; intros Hp; subst p2.
  f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.

Record NodeRef {p : Syntax.Program} (idx : ProgramIndex p) : Type := MakeNodeRef {
  nr_file  : FileRef p;
  nr_local : positive;
  nr_valid : occ_ofb idx (fr_path nr_file) nr_local = true
}.
Arguments MakeNodeRef {p idx}. Arguments nr_file {p idx}. Arguments nr_local {p idx}. Arguments nr_valid {p idx}.

Definition node_ref_file {p} {idx : ProgramIndex p} (r : NodeRef idx) : FileRef p := nr_file r.
Definition node_ref_local {p} {idx : ProgramIndex p} (r : NodeRef idx) : positive := nr_local r.
Definition node_ref_key {p} {idx : ProgramIndex p} (r : NodeRef idx) : Key := MakeKey (fr_path (nr_file r)) (nr_local r).

Lemma node_ref_valid {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  occ_ofb idx (fr_path (nr_file r)) (nr_local r) = true.
Proof. destruct r as [fr l v]; exact v. Qed.

(* the retained metadata a reference designates: read from the index table, total by its validity proof *)
Definition node_meta {p} {idx : ProgramIndex p} (r : NodeRef idx) : Meta :=
  option_get (meta_of idx (fr_path (nr_file r)) (nr_local r)) (occ_ofb_some p idx _ _ (nr_valid r)).

Lemma node_meta_eq {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  meta_of idx (fr_path (nr_file r)) (nr_local r) = Some (node_meta r).
Proof. unfold node_meta. apply option_get_some. Qed.

Definition node_kind {p} {idx : ProgramIndex p} (r : NodeRef idx) : Kind := kind (node_meta r).
Definition node_role {p} {idx : ProgramIndex p} (r : NodeRef idx) : Role := role (node_meta r).
Definition node_subtree_end {p} {idx : ProgramIndex p} (r : NodeRef idx) : positive := subtree_end (node_meta r).

Lemma node_ref_key_eq {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  node_ref_key r = MakeKey (file_ref_path (node_ref_file r)) (node_ref_local r).
Proof. reflexivity. Qed.

(* two references with equal file and equal local id are equal (validity is proof-irrelevant here) *)
Lemma node_ref_ext {p} {idx : ProgramIndex p} (r1 r2 : NodeRef idx) :
  nr_file r1 = nr_file r2 -> nr_local r1 = nr_local r2 -> r1 = r2.
Proof.
  destruct r1 as [f1 l1 v1], r2 as [f2 l2 v2]; cbn; intros Hf Hl; subst f2 l2.
  f_equal. apply Eqdep_dec.UIP_dec, Bool.bool_dec.
Qed.

Lemma node_ref_key_inj {p} {idx : ProgramIndex p} (r1 r2 : NodeRef idx) : node_ref_key r1 = node_ref_key r2 -> r1 = r2.
Proof.
  unfold node_ref_key. intros H. injection H as Hp Hl.
  apply node_ref_ext; [ apply file_ref_ext; exact Hp | exact Hl ].
Qed.

(* Locate a file by its path, retaining the membership proof. *)
Definition file_of_path (p : Syntax.Program) (fp : FilePath.T) : option (FileRef p) :=
  match Syntax.file_mem fp (Syntax.files p) as b
        return Syntax.file_mem fp (Syntax.files p) = b -> option (FileRef p) with
  | true  => fun H => Some (MakeFileRef fp H)
  | false => fun _ => None
  end eq_refl.

Lemma file_of_path_sound : forall p fp fr,
  file_of_path p fp = Some fr -> file_ref_path fr = fp.
Proof.
  intros p fp fr. unfold file_of_path.
  generalize (@eq_refl bool (Syntax.file_mem fp (Syntax.files p))).
  destruct (Syntax.file_mem fp (Syntax.files p)) at 2 3; intros e H; [|discriminate H].
  injection H as <-. reflexivity.
Qed.

Lemma file_of_path_complete : forall p fr,
  file_of_path p (fr_path fr) = Some fr.
Proof.
  intros p fr. unfold file_of_path.
  generalize (@eq_refl bool (Syntax.file_mem (fr_path fr) (Syntax.files p))).
  destruct (Syntax.file_mem (fr_path fr) (Syntax.files p)) at 2 3; intros e.
  - f_equal. apply file_ref_ext. reflexivity.
  - exfalso. rewrite (fr_memb fr) in e. discriminate e.
Qed.

Lemma file_of_path_source : forall p fp fr,
  file_of_path p fp = Some fr -> Syntax.find_file fp (Syntax.files p) = Some (file_ref_source fr).
Proof.
  intros p fp fr H. pose proof (file_of_path_sound p fp fr H) as Hp.
  unfold file_ref_path in Hp. unfold file_ref_source. rewrite <- Hp. apply file_ref_find.
Qed.

(* resolve a key to the reference it names in the retained index, when both its file and local id are real *)
Definition ref_of_key {p : Syntax.Program} (idx : ProgramIndex p) (k : Key) : option (NodeRef idx) :=
  match file_of_path p (key_path k) with
  | Some fr =>
      match occ_ofb idx (fr_path fr) (key_local k) as b
            return occ_ofb idx (fr_path fr) (key_local k) = b -> option (NodeRef idx) with
      | true  => fun H => Some (MakeNodeRef fr (key_local k) H)
      | false => fun _ => None
      end eq_refl
  | None => None
  end.

Lemma ref_of_key_sound : forall p (idx : ProgramIndex p) k r, ref_of_key idx k = Some r -> node_ref_key r = k.
Proof.
  intros p idx k r. unfold ref_of_key. destruct (file_of_path p (key_path k)) as [fr|] eqn:Efr; [|discriminate].
  generalize (@eq_refl bool (occ_ofb idx (fr_path fr) (key_local k))).
  destruct (occ_ofb idx (fr_path fr) (key_local k)) at 2 3; intros e H; [|discriminate H].
  injection H as <-. unfold node_ref_key. cbn.
  apply file_of_path_sound in Efr. unfold file_ref_path in Efr.
  destruct k as [kp kl]; cbn in *. rewrite Efr. reflexivity.
Qed.

Lemma ref_of_key_complete : forall p (idx : ProgramIndex p) r, ref_of_key idx (node_ref_key r) = Some r.
Proof.
  intros p idx r. unfold ref_of_key, node_ref_key. cbn [key_path key_local].
  rewrite (file_of_path_complete p (nr_file r)).
  generalize (@eq_refl bool (occ_ofb idx (fr_path (nr_file r)) (nr_local r))).
  destruct (occ_ofb idx (fr_path (nr_file r)) (nr_local r)) at 2 3; intros e.
  - f_equal. apply node_ref_ext; reflexivity.
  - exfalso. rewrite (nr_valid r) in e. discriminate e.
Qed.

End Snapshot.
