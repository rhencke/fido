(* Bindings — object identity, lexical scopes, establisher sites, and ordinary-name resolution with shadowing. *)

From Stdlib Require Import PArith NArith List Bool Lia String.
From Fido Require Import Collections FilePath Names Syntax Index.
Import ListNotations.
Local Open Scope positive_scope.

(* an object is a predeclared entity or a source object named by its establisher's exact retained occurrence *)
Inductive ObjectRef {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : Index.Snapshot.NodeRef idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx}. Arguments SourceObject {p idx}.

Definition object_key {p} {idx : Index.ProgramIndex p} (o : ObjectRef idx) : option Index.Key :=
  match o with PredeclaredObject _ => None | SourceObject r => Some (Index.Snapshot.node_ref_key r) end.

Definition object_eqb {p} {idx : Index.ProgramIndex p} (a b : ObjectRef idx) : bool :=
  match a, b with
  | PredeclaredObject na, PredeclaredObject nb => Names.predeclared_eqb na nb
  | SourceObject ra, SourceObject rb           =>
      Index.key_equalb (Index.Snapshot.node_ref_key ra) (Index.Snapshot.node_ref_key rb)
  | _, _ => false
  end.

Lemma object_eqb_spec : forall p (idx : Index.ProgramIndex p) (a b : ObjectRef idx), object_eqb a b = true <-> a = b.
Proof.
  intros p idx [na|ra] [nb|rb]; cbn; split; try discriminate.
  - intros H. apply Names.predeclared_eqb_spec in H. subst. reflexivity.
  - intros H. injection H as <-. apply Names.predeclared_eqb_spec. reflexivity.
  - intros H. apply Index.key_equalb_spec in H. apply Index.Snapshot.node_ref_key_inj in H. subst. reflexivity.
  - intros H. injection H as <-. apply Index.key_equalb_spec. reflexivity.
Qed.

(* lexical scopes: the predeclared universe, a package directory, and a func body's retained block occurrence *)
Inductive ScopeId {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredScope
| PackageScope : string -> ScopeId idx
| BlockScope   : Index.Snapshot.NodeRef idx -> ScopeId idx.
Arguments PredeclaredScope {p idx}. Arguments PackageScope {p idx}. Arguments BlockScope {p idx}.

Definition scope_eqb {p} {idx : Index.ProgramIndex p} (a b : ScopeId idx) : bool :=
  match a, b with
  | PredeclaredScope, PredeclaredScope => true
  | PackageScope da, PackageScope db   => String.eqb da db
  | BlockScope ra, BlockScope rb       =>
      Index.key_equalb (Index.Snapshot.node_ref_key ra) (Index.Snapshot.node_ref_key rb)
  | _, _ => false
  end.

Lemma scope_eqb_spec : forall p (idx : Index.ProgramIndex p) (a b : ScopeId idx), scope_eqb a b = true <-> a = b.
Proof.
  intros p idx [|da|ra] [|db|rb]; cbn; split; try discriminate; try reflexivity.
  - intros H. apply String.eqb_eq in H. subst. reflexivity.
  - intros H. injection H as <-. apply String.eqb_eq. reflexivity.
  - intros H. apply Index.key_equalb_spec in H. apply Index.Snapshot.node_ref_key_inj in H. subst. reflexivity.
  - intros H. injection H as <-. apply Index.key_equalb_spec. reflexivity.
Qed.

Definition block_dir {p} {idx : Index.ProgramIndex p} (r : Index.Snapshot.NodeRef idx) : string :=
  FilePath.parent (Index.key_path (Index.Snapshot.node_ref_key r)).

Definition scope_parent {p} {idx : Index.ProgramIndex p} (s : ScopeId idx) : option (ScopeId idx) :=
  match s with
  | PredeclaredScope => None
  | PackageScope _   => Some PredeclaredScope
  | BlockScope r     => Some (PackageScope (block_dir r))
  end.

(* the enclosing scopes of a scope, innermost first — the exact, finite chain *)
Definition scope_chain {p} {idx : Index.ProgramIndex p} (s : ScopeId idx) : list (ScopeId idx) :=
  match s with
  | PredeclaredScope => [PredeclaredScope]
  | PackageScope d   => [PackageScope d; PredeclaredScope]
  | BlockScope r     => [BlockScope r; PackageScope (block_dir r); PredeclaredScope]
  end.

Definition Encloses {p} {idx : Index.ProgramIndex p} (outer inner : ScopeId idx) : Prop :=
  In outer (scope_chain inner).

Lemma encloses_self : forall p (idx : Index.ProgramIndex p) (s : ScopeId idx), Encloses s s.
Proof. intros p idx s; unfold Encloses; destruct s; simpl; left; reflexivity. Qed.

Lemma encloses_parent : forall p (idx : Index.ProgramIndex p) (outer inner par : ScopeId idx),
  scope_parent inner = Some par -> Encloses outer par -> Encloses outer inner.
Proof.
  intros p idx outer inner par Hp Hen. unfold Encloses in *.
  destruct inner as [|d|r]; cbn [scope_parent] in Hp; try discriminate;
    injection Hp as <-; cbn [scope_chain] in *; right; exact Hen.
Qed.

Section WithProgram.
Variable p : Syntax.Program.
Variable idx : Index.ProgramIndex p.

(* build the retained reference a real occurrence key names; a gathered key is always real, so this is total *)
Definition ref_at (path : FilePath.T) (id : positive) : option (Index.Snapshot.NodeRef idx) :=
  Index.Snapshot.ref_of_key idx (Index.MakeKey path id).

(* the func-body block windows [id, subtree_end] and direct block-statement windows, over a computed occ list *)
Definition block_windows (occs : list (positive * Index.Occurrence)) : list (positive * positive) :=
  fold_right (fun idocc acc =>
     match Index.occurrence_kind (snd idocc) with
     | Index.BlockKind => (fst idocc, Index.occurrence_subtree_end (snd idocc)) :: acc
     | _ => acc end) [] occs.

Definition stmt_windows (occs : list (positive * Index.Occurrence)) : list (positive * positive) :=
  fold_right (fun idocc acc =>
     match Index.occurrence_role (snd idocc) with
     | Index.BlockStatement _ => (fst idocc, Index.occurrence_subtree_end (snd idocc)) :: acc
     | _ => acc end) [] occs.

(* the innermost block window strictly containing [id]; ties resolved to the latest-starting (nearest) block *)
Definition nearest_block (bw : list (positive * positive)) (id : positive) : option (positive * positive) :=
  fold_right (fun w acc =>
     let '(bid, bend) := w in
     if andb (Pos.ltb bid id) (Pos.leb id bend)
     then match acc with Some (a, _) => if Pos.ltb a bid then Some (bid, bend) else acc | None => Some (bid, bend) end
     else acc)
   None bw.

Definition scope_of_id (bw : list (positive * positive)) (path : FilePath.T) (id : positive) : ScopeId idx :=
  match nearest_block bw id with
  | Some (bid, _) => match ref_at path bid with Some r => BlockScope r | None => PackageScope (FilePath.parent path) end
  | None => PackageScope (FilePath.parent path)
  end.

(* the end of the block statement enclosing [id]; [id] itself when [id] is not inside a block statement *)
Definition stmt_end_of (sw : list (positive * positive)) (id : positive) : positive :=
  fold_right (fun w acc =>
     let '(sid, send) := w in if andb (Pos.leb sid id) (Pos.leb id send) then send else acc)
   id sw.

(* an object-establisher: a BNamed binder in a spec-name or short-lhs position; a blank establishes nothing *)
Definition binder_spelling (occ : Index.Occurrence) : option (string * bool) :=
  match Index.view_binding_name occ with
  | Some (Syntax.BNamed n) =>
      match Index.occurrence_role occ with
      | Index.SpecName _ => Some (Names.ordinary_spelling n, false)
      | Index.ShortLhs _ => Some (Names.ordinary_spelling n, true)
      | _ => None
      end
  | _ => None
  end.

Record Establisher := MkEst {
  est_ref      : Index.Snapshot.NodeRef idx;
  est_spelling : string;
  est_scope    : ScopeId idx;
  est_short    : bool;
  est_stmt_end : positive;
  est_block    : option (positive * positive)   (* the containing block window, for O(1) use-containment *)
}.

Definition est_key (e : Establisher) : Index.Key := Index.Snapshot.node_ref_key (est_ref e).

Definition file_establishers (b : FilePath.T * Syntax.File) : list Establisher :=
  let occs := Index.occurrences_file (snd b) in
  let bw   := block_windows occs in
  let sw   := stmt_windows occs in
  fold_right (fun idocc acc =>
     match binder_spelling (snd idocc) with
     | Some (sp, sh) =>
         match ref_at (fst b) (fst idocc) with
         | Some r => MkEst r sp (scope_of_id bw (fst b) (fst idocc)) sh (stmt_end_of sw (fst idocc))
                          (nearest_block bw (fst idocc)) :: acc
         | None => acc
         end
     | None => acc end)
   [] occs.

Definition establishers : list Establisher :=
  flat_map file_establishers (Syntax.file_bindings (Syntax.files p)).

(* an establisher is visible to a use only after its declaring statement finishes (block scopes only) *)
Definition visible_to (e : Establisher) (use_id : positive) : bool :=
  match est_block e with Some _ => Pos.ltb (est_stmt_end e) use_id | None => true end.

(* does [e]'s scope contain a use? block = same file within the block window; package = same directory *)
Definition scope_contains (e : Establisher) (use_path : FilePath.T) (use_id : positive) : bool :=
  match est_block e with
  | Some (lo, hi) =>
      andb (FilePath.equalb (Index.key_path (est_key e)) use_path) (andb (Pos.leb lo use_id) (Pos.leb use_id hi))
  | None => String.eqb (FilePath.parent (Index.key_path (est_key e))) (FilePath.parent use_path)
  end.

Definition block_scoped (e : Establisher) : bool := match est_block e with Some _ => true | None => false end.

(* the establishers of a spelling whose scope contains and is visible to a use *)
Definition visible_here (es : list Establisher) (n : string) (use_path : FilePath.T) (use_id : positive)
  : list Establisher :=
  filter (fun e => andb (andb (String.eqb (est_spelling e) n) (scope_contains e use_path use_id)) (visible_to e use_id)) es.

(* the earliest establisher by local id — the definite binder when a scope holds exactly one of a spelling *)
Definition earliest (es : list Establisher) : option Establisher :=
  fold_right (fun e acc =>
     match acc with
     | None => Some e
     | Some a => if Pos.ltb (Index.key_local (est_key e)) (Index.key_local (est_key a)) then Some e else acc
     end) None es.

(* a use resolves to the nearest visible enclosing source object of its spelling, else the predeclared one *)
Definition resolve (es : list Establisher) (use_path : FilePath.T) (use_id : positive) (n : string)
  : option (ObjectRef idx) :=
  let cands := visible_here es n use_path use_id in
  match earliest (filter block_scoped cands) with
  | Some e => Some (SourceObject (est_ref e))
  | None =>
      match earliest (filter (fun e => negb (block_scoped e)) cands) with
      | Some e => Some (SourceObject (est_ref e))
      | None =>
          match Names.classify_predeclared n with
          | Some pn => Some (PredeclaredObject pn)
          | None    => None
          end
      end
  end.

(* the spelling a name use denotes (only a bare [Name] use has one) *)
Definition use_spelling (occ : Index.Occurrence) : option string :=
  match Index.view_expr occ with
  | Some (Syntax.Name n) => Some (Names.ordinary_spelling n)
  | _ => None
  end.

(* the short-declaration disposition of a left occurrence: a blank, a new object, or a reuse of an earlier one *)
Inductive ShortDisposition : Type :=
| ShortBlank
| ShortNew
| ShortReuse : Index.Snapshot.NodeRef idx -> ShortDisposition.

(* the establishers of a spelling in one scope, other than [self], declared strictly before [self] *)
Definition prior_establishers (es : list Establisher) (sc : ScopeId idx) (n : string) (self : Establisher)
  : list Establisher :=
  filter (fun e => andb (andb (String.eqb (est_spelling e) n) (scope_eqb (est_scope e) sc))
                        (Pos.ltb (Index.key_local (est_key e)) (Index.key_local (est_key self)))) es.

(* is [e] a short-lhs establisher that reuses an earlier binder of its spelling in the same scope? *)
Definition short_disposition (es : list Establisher) (e : Establisher) : ShortDisposition :=
  if est_short e then
     match earliest (prior_establishers es (est_scope e) (est_spelling e) e) with
     | Some prior => ShortReuse (est_ref prior)
     | None       => ShortNew
     end
  else ShortNew.

(* a full (non-short) establisher redeclared where an earlier binder of its spelling already stands *)
Definition redeclares (es : list Establisher) (e : Establisher) : bool :=
  andb (negb (est_short e))
       (negb (match prior_establishers es (est_scope e) (est_spelling e) e with [] => true | _ => false end)).

End WithProgram.

Arguments MkEst {p idx}. Arguments est_ref {p idx}. Arguments est_spelling {p idx}. Arguments est_scope {p idx}.
Arguments est_short {p idx}. Arguments est_stmt_end {p idx}. Arguments est_key {p idx}.
Arguments ShortBlank {p idx}. Arguments ShortNew {p idx}. Arguments ShortReuse {p idx}.
Arguments Establisher {p} idx.
