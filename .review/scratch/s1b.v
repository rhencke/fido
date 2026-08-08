
(* ── §2.1 The scope forest ─────────────────────────────────────────────────── *)
Parameter LexicalScopeRef : SyntaxProgram -> Type.
Parameter lexical_scope_package : forall {p}, LexicalScopeRef p -> PackageRef p.

Inductive ScopeId (p : SyntaxProgram) : Type :=
| PredeclaredScope : ScopeId p
| PackageScope     : PackageRef p -> ScopeId p
| LexicalScope     : LexicalScopeRef p -> ScopeId p.

Definition scope_parent {p} (s : ScopeId p) : option (ScopeId p) :=
  match s with
  | PredeclaredScope _ => None
  | PackageScope _ _   => Some (PredeclaredScope p)
  | LexicalScope _ b   => Some (PackageScope p (lexical_scope_package b))
  end.

Inductive Encloses {p} : ScopeId p -> ScopeId p -> Prop :=
| EnclosesSelf   : forall s, Encloses s s
| EnclosesParent : forall outer inner parent,
    scope_parent inner = Some parent -> Encloses outer parent -> Encloses outer inner.

Inductive ScopeStart : Type :=
| StartWholePackage | StartAfterSpec | StartAtOwnIdentifier | StartAfterStatement | StartOutermost.

Inductive DeclContext : Type :=
| PackageConstDecl | PackageVarDecl | PackageTypeDecl
| LocalConstDecl | LocalVarDecl | LocalTypeDecl
| ShortDecl | PredeclaredDecl.

Definition scope_start (c : DeclContext) : ScopeStart :=
  match c with
  | PackageConstDecl | PackageVarDecl | PackageTypeDecl => StartWholePackage
  | LocalConstDecl | LocalVarDecl => StartAfterSpec
  | LocalTypeDecl => StartAtOwnIdentifier
  | ShortDecl => StartAfterStatement
  | PredeclaredDecl => StartOutermost
  end.

Definition PackageInitReserved (c : DeclContext) (n : string) : Prop :=
  (c = PackageConstDecl \/ c = PackageVarDecl \/ c = PackageTypeDecl) /\ n = "init"%string.

