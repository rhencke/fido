(* Bindings — object identity, lexical scopes, establisher sites, and ordinary-name resolution with shadowing. *)

From Stdlib Require Import PArith NArith List Bool Lia String.
From Fido Require Import Collections FilePath Names Syntax Index.
Import ListNotations.
Local Open Scope positive_scope.

(* An object: a predeclared entity, or a source object keyed by its establisher's exact occurrence key. *)
Inductive ObjectRef : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef
| SourceObject      : Index.Key -> ObjectRef.

Definition object_eqb (a b : ObjectRef) : bool :=
  match a, b with
  | PredeclaredObject na, PredeclaredObject nb => Names.predeclared_eqb na nb
  | SourceObject ka, SourceObject kb           => Index.key_equalb ka kb
  | _, _ => false
  end.

Lemma object_eqb_spec : forall a b, object_eqb a b = true <-> a = b.
Proof.
  intros [na|ka] [nb|kb]; cbn; split; try discriminate.
  - intros H. apply Names.predeclared_eqb_spec in H. subst. reflexivity.
  - intros H. injection H as <-. apply Names.predeclared_eqb_spec. reflexivity.
  - intros H. apply Index.key_equalb_spec in H. subst. reflexivity.
  - intros H. injection H as <-. apply Index.key_equalb_spec. reflexivity.
Qed.

(*  Proof-free object-kind view (a diagnostic classifier, carries no evidence)  *)
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Definition predeclared_kind (n : Names.PredeclaredName) : ObjectKind :=
  match n with
  | Names.PAny | Names.PBool | Names.PByte | Names.PComparable | Names.PComplex64 | Names.PComplex128
  | Names.PError | Names.PFloat32 | Names.PFloat64
  | Names.PInt | Names.PInt8 | Names.PInt16 | Names.PInt32 | Names.PInt64 | Names.PRune | Names.PString
  | Names.PUint | Names.PUint8 | Names.PUint16 | Names.PUint32 | Names.PUint64 | Names.PUintptr => TypeObject
  | Names.PTrue | Names.PFalse | Names.PIota => ConstantObject
  | Names.PNil => NilObject
  | Names.PAppend | Names.PCap | Names.PClear | Names.PClose | Names.PComplex | Names.PCopy | Names.PDelete
  | Names.PImag | Names.PLen | Names.PMake | Names.PMax | Names.PMin | Names.PNew | Names.PPanic
  | Names.PPrint | Names.PPrintln | Names.PReal | Names.PRecover => BuiltinObject
  end.

Definition object_kind (o : ObjectRef) : ObjectKind :=
  match o with
  | PredeclaredObject n => predeclared_kind n
  | SourceObject _      => VariableObject   (* the proof-free classifier; the phase refines source meaning *)
  end.

(* Lexical scopes: the predeclared universe, the package directory, and a func body's block. *)
Inductive ScopeId : Type :=
| PredeclaredScope
| PackageScope : string -> ScopeId
| BlockScope   : Index.Key -> ScopeId.

Definition scope_eqb (a b : ScopeId) : bool :=
  match a, b with
  | PredeclaredScope, PredeclaredScope => true
  | PackageScope da, PackageScope db   => String.eqb da db
  | BlockScope ka, BlockScope kb       => Index.key_equalb ka kb
  | _, _ => false
  end.

Lemma scope_eqb_spec : forall a b, scope_eqb a b = true <-> a = b.
Proof.
  intros [|da|ka] [|db|kb]; cbn; split; try discriminate; try reflexivity.
  - intros H. apply String.eqb_eq in H. subst. reflexivity.
  - intros H. injection H as <-. apply String.eqb_eq. reflexivity.
  - intros H. apply Index.key_equalb_spec in H. subst. reflexivity.
  - intros H. injection H as <-. apply Index.key_equalb_spec. reflexivity.
Qed.

Definition scope_dir (k : Index.Key) : string := FilePath.parent (Index.key_path k).

Definition scope_parent (s : ScopeId) : option ScopeId :=
  match s with
  | PredeclaredScope => None
  | PackageScope _   => Some PredeclaredScope
  | BlockScope k     => Some (PackageScope (scope_dir k))
  end.

(* The enclosing scopes of a scope, innermost first — the exact, finite chain. *)
Definition scope_chain (s : ScopeId) : list ScopeId :=
  match s with
  | PredeclaredScope => [PredeclaredScope]
  | PackageScope d   => [PackageScope d; PredeclaredScope]
  | BlockScope k     => [BlockScope k; PackageScope (scope_dir k); PredeclaredScope]
  end.

Definition Encloses (outer inner : ScopeId) : Prop := In outer (scope_chain inner).

Lemma encloses_self : forall s, Encloses s s.
Proof. intros s; unfold Encloses; destruct s; simpl; left; reflexivity. Qed.

Lemma encloses_parent : forall outer inner par,
  scope_parent inner = Some par -> Encloses outer par -> Encloses outer inner.
Proof.
  intros outer inner par Hp Hen. unfold Encloses in *.
  destruct inner as [|d|k]; cbn [scope_parent] in Hp; try discriminate;
    injection Hp as <-; cbn [scope_chain] in *; right; exact Hen.
Qed.

Section WithProgram.
Variable p : Syntax.Program.

(* Every occurrence of every file, tagged by its exact key. *)
Definition file_occurrences (b : FilePath.T * Syntax.File) : list (Index.Key * Index.Occurrence) :=
  List.map (fun idocc => (Index.MakeKey (fst b) (fst idocc), snd idocc)) (Index.occurrences_file (snd b)).

Definition program_occurrences : list (Index.Key * Index.Occurrence) :=
  flat_map file_occurrences (Syntax.file_bindings (Syntax.files p)).

(* An occurrence's scope: the innermost block whose subtree window strictly contains its id, else package. *)
Definition file_block_windows (f : Syntax.File) : list (positive * positive) :=
  fold_right (fun idocc acc =>
     match Index.occurrence_kind (snd idocc) with
     | Index.BlockKind => (fst idocc, Index.occurrence_subtree_end (snd idocc)) :: acc
     | _ => acc end) [] (Index.occurrences_file f).

Definition scope_of_id (path : FilePath.T) (f : Syntax.File) (id : positive) : ScopeId :=
  fold_right (fun w acc =>
     let '(bid, bend) := w in
     if andb (Pos.ltb bid id) (Pos.leb id bend) then BlockScope (Index.MakeKey path bid) else acc)
   (PackageScope (FilePath.parent path)) (file_block_windows f).

(* An object-establisher: a BNamed binder in a spec-name or short-lhs position; a blank establishes nothing. *)
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
  est_key      : Index.Key;
  est_spelling : string;
  est_scope    : ScopeId;
  est_short    : bool
}.

Definition file_establishers (b : FilePath.T * Syntax.File) : list Establisher :=
  fold_right (fun idocc acc =>
     match binder_spelling (snd idocc) with
     | Some (sp, sh) =>
         MkEst (Index.MakeKey (fst b) (fst idocc)) sp (scope_of_id (fst b) (snd b) (fst idocc)) sh :: acc
     | None => acc end)
   [] (Index.occurrences_file (snd b)).

Definition establishers : list Establisher :=
  flat_map file_establishers (Syntax.file_bindings (Syntax.files p)).

(* A use resolves to the nearest enclosing source object of its spelling, else the predeclared one, else none. *)
Definition establishers_in_scope (sc : ScopeId) (n : string) : list Establisher :=
  filter (fun e => andb (String.eqb (est_spelling e) n) (scope_eqb (est_scope e) sc)) establishers.

Definition earliest (es : list Establisher) : option Establisher :=
  fold_right (fun e acc =>
     match acc with
     | None => Some e
     | Some a => if Pos.ltb (Index.key_local (est_key e)) (Index.key_local (est_key a)) then Some e else acc
     end) None es.

Fixpoint resolve_in_chain (chain : list ScopeId) (n : string) : option Index.Key :=
  match chain with
  | [] => None
  | sc :: rest =>
      match earliest (establishers_in_scope sc n) with
      | Some e => Some (est_key e)
      | None   => resolve_in_chain rest n
      end
  end.

Definition resolve (use_scope : ScopeId) (n : string) : option ObjectRef :=
  match resolve_in_chain (scope_chain use_scope) n with
  | Some k => Some (SourceObject k)
  | None =>
      match Names.classify_predeclared n with
      | Some pn => Some (PredeclaredObject pn)
      | None    => None
      end
  end.

(* The spelling a name use denotes (only a bare [Name] use has one). *)
Definition use_spelling (occ : Index.Occurrence) : option string :=
  match Index.view_expr occ with
  | Some (Syntax.Name n) => Some (Names.ordinary_spelling n)
  | _ => None
  end.

(* Resolve a name use at its exact site. *)
Definition resolve_use (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : option ObjectRef :=
  match use_spelling occ with
  | Some n => resolve (scope_of_id path f id) n
  | None   => None
  end.

End WithProgram.
