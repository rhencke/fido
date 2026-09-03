-- Port of Syntax.v (lean/README.md).
import Fido.FilePath
import Fido.Collections
import Fido.ModulePath
import Fido.Version
import Fido.Float
import Fido.Names

/-! divergences:
  * `N` (the binary naturals of `IntegerLiteral`) is `Nat`: the README maps `nat` to `Nat`, and `N` carries
    the same values under a different representation.
  * `Module FileMap := Collections.FileMap` / `Module FileFacts := Collections.FileFacts`: Lean has no module
    aliasing, so `FileMap` and `FileFacts` are namespaces that `export` exactly the names Collections.lean
    exposes under those module names (the pattern Collections itself uses); `Files` is then `FileMap.t File`
    as in the `.v`.
  * `List.In` / `NoDup` / `Permutation` / `List.Forall` are `∈` / `List.Nodup` / `List.Perm` / `∀ x ∈ l, P x`
    (README).  `Expr_ind'`'s `List.Forall P args` hypothesis is therefore `∀ x ∈ args, P x`, and its body is
    the nested recursor `Expr.rec` with the list motive `fun es => ∀ x ∈ es, P x` — Rocq's inner
    `fix args_ind`.  `SetoidList.InA_alt` disappears: Collections renders `InA eq_key_elt (x, e) l` as
    `(x, e) ∈ l`, so `file_bindings_find` / `find_file_bindings` are the two `FileFacts` iffs composed.
  * Rocq's `if b then … else …` on a `bool` is `bif` (`cond`), so `files_of_nodes` still cases on the boolean.
  * `Record`s are `structure`s and data `Inductive`s with constructor arguments keep their constructors, both
    with `genInjectivity` / `genSizeOfSpec` off (the auto-generated lemmas would be the module's only
    `propext` users outside the map library; Rocq generates none), plus `export` of every constructor and
    projection so `path n`, `source n`, `files p`, `Name n`, `MakeBlock l` read as in the `.v`.  `ImportSpec`
    is the constructor-free `inductive ImportSpec : Type`.
  * Rocq's `in_map` / `in_map_iff` are two private axiom-free inductions on `∈` (core's `List.mem_map_of_mem`
    / `List.mem_map` carry `propext` and `Quot.sound`); `Permutation_in` is core's `List.Perm.mem_iff`, which
    carries `propext` only.  `rw` with an `Iff` would add `propext`, so the iff-chains are `Iff.trans`.
  * CORE FINDING (Collections): every constant whose type or body mentions `Files` — a `Std.TreeMap` over
    `FilePathOrder` — audits classical, `Files` itself included: `Std.TreeMap` insert / lookup / contains /
    toList and the `FilePathOrder` order instances reach `Classical.choice` inside core.  So `empty_files` …
    `build_program_some_iff_unique` and `Program` (whose `files` field has that type, hence its generated
    `rec` / `casesOn` / `noConfusion`) all do, for that reason alone; no proof in this module adds one.  The
    AST (`BindingName` … `FileNode`, `ModuleSpec`), `Expr_ind'`, `type_expr_ident`, `main_source` and
    `main_file_node` are axiom-free.
-/

namespace Fido.Syntax

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A binding position names an ordinary identifier or is blank; blank establishes no object. -/
inductive BindingName : Type
  | BNamed : Names.OrdinaryIdentifier → BindingName
  | BBlank : BindingName

export BindingName (BNamed BBlank)

inductive UnaryOp : Type
  | UnaryMinus

export UnaryOp (UnaryMinus)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Numeric source literals are magnitudes; a negative value is exactly one `Unary UnaryMinus`. -/
inductive Literal : Type
  | IntegerLiteral : Nat → Literal
  | FloatLiteral : Float.NonNegativeDecimal → Literal
  | StringLiteral : Str → Literal

export Literal (IntegerLiteral FloatLiteral StringLiteral)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A type use names an ordinary source identifier; predeclared meaning is a later binding fact. -/
inductive TypeExpr : Type
  | NamedType : Names.OrdinaryIdentifier → TypeExpr

export TypeExpr (NamedType)

def type_expr_ident (t : TypeExpr) : Names.OrdinaryIdentifier := match t with | NamedType n => n

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive Expr : Type
  | Name : Names.OrdinaryIdentifier → Expr
  | LiteralExpr : Literal → Expr
  | Unary : UnaryOp → Expr → Expr
  | Application : Expr → List Expr → Expr

export Expr (Name LiteralExpr Unary Application)

/-- The default `Expr` recursor is too weak under the nested `list`; this carries a `Forall` over arguments. -/
theorem Expr_ind' (P : Expr → Prop)
    (HName : ∀ n, P (Name n))
    (HLit : ∀ l, P (LiteralExpr l))
    (HUnary : ∀ op e, P e → P (Unary op e))
    (HApp : ∀ head args, P head → (∀ x ∈ args, P x) → P (Application head args))
    (e : Expr) : P e :=
  Expr.rec (motive_1 := fun e => P e) (motive_2 := fun es => ∀ x ∈ es, P x)
    HName HLit HUnary HApp
    (fun _ hx => nomatch hx)
    (fun _ _ ihx ihxs y hy => by
      cases hy with
      | head => exact ihx
      | tail _ h => exact ihxs y h)
    e

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A const spec binds one or more names to an explicit initializer or inherits the preceding one. -/
inductive ConstInitializer : Type
  | ExplicitConstInit : Option TypeExpr → Collections.NonEmpty Expr → ConstInitializer
  | InheritedConstInit : ConstInitializer

export ConstInitializer (ExplicitConstInit InheritedConstInit)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure ConstSpec : Type where
  MakeConstSpec ::
  const_names : Collections.NonEmpty BindingName
  const_init : ConstInitializer

export ConstSpec (MakeConstSpec const_names const_init)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A var spec is a type-only declaration or one or more names bound to initializer values. -/
inductive VarInitializer : Type
  | VarTypeOnly : TypeExpr → VarInitializer
  | VarValues : Option TypeExpr → Collections.NonEmpty Expr → VarInitializer

export VarInitializer (VarTypeOnly VarValues)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure VarSpec : Type where
  MakeVarSpec ::
  var_names : Collections.NonEmpty BindingName
  var_init : VarInitializer

export VarSpec (MakeVarSpec var_names var_init)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A type spec is an alias or a defined type over one target type use. -/
inductive TypeSpec : Type
  | AliasSpec : BindingName → TypeExpr → TypeSpec
  | DefSpec : BindingName → TypeExpr → TypeSpec

export TypeSpec (AliasSpec DefSpec)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A declaration groups specs; the group is a list because an empty group is valid Go. -/
inductive Declaration : Type
  | ConstDecl : List ConstSpec → Declaration
  | VarDecl : List VarSpec → Declaration
  | TypeDecl : List TypeSpec → Declaration

export Declaration (ConstDecl VarDecl TypeDecl)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A statement is an expression, a local declaration, or a short variable declaration. -/
inductive Stmt : Type
  | ExprStmt : Expr → Stmt
  | DeclarationStmt : Declaration → Stmt
  | ShortVarDecl : Collections.NonEmpty BindingName → Collections.NonEmpty Expr → Stmt

export Stmt (ExprStmt DeclarationStmt ShortVarDecl)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive Block : Type
  | MakeBlock : List Stmt → Block

export Block (MakeBlock)

/-- The package clause as source syntax; only the canonical package main is representable. -/
inductive PackageClause : Type
  | MainPackage

export PackageClause (MainPackage)

/-- An import spec: the type is empty, so `List ImportSpec` can only be `[]`. -/
inductive ImportSpec : Type

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A top-level declaration is a package-level declaration or the main function body. -/
inductive TopLevelDecl : Type
  | TopDeclaration : Declaration → TopLevelDecl
  | Main : Block → TopLevelDecl

export TopLevelDecl (TopDeclaration Main)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure File : Type where
  MakeFile ::
  package : PackageClause
  imports : List ImportSpec
  declarations : List TopLevelDecl

export File (MakeFile package imports declarations)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A construction and view value pairing a path with its source; the map key below is the path authority. -/
structure FileNode : Type where
  MakeFileNode ::
  path : FilePath.T
  source : File

export FileNode (MakeFileNode path source)

/-! ### `Module FileMap := Collections.FileMap.` / `Module FileFacts := Collections.FileFacts.` -/

namespace FileMap
export Collections.FileMap (key t empty add find remove mem map elements cardinal fold MapsTo In Empty Equal
  eq_key eq_key_elt lt_key find_1 find_2 mem_1 mem_2 empty_1 add_1 add_2 add_3 remove_1 remove_2 remove_3
  elements_1 elements_2 elements_3w elements_3 cardinal_1 fold_1 map_1 map_2)
end FileMap

namespace FileFacts
export Collections.FileFacts (find_mapsto_iff elements_mapsto_iff mem_in_iff in_find_iff empty_o add_o
  add_eq_o add_neq_o add_in_iff add_mapsto_iff remove_o remove_eq_o remove_neq_o map_o map_mapsto_iff)
end FileFacts

abbrev Files : Type := FileMap.t File

def empty_files : Files := FileMap.empty File
def find_file (p : FilePath.T) (fm : Files) : Option File := FileMap.find p fm
def maps_to_file (p : FilePath.T) (sf : File) (fm : Files) : Prop := FileMap.MapsTo p sf fm
def file_mem (p : FilePath.T) (fm : Files) : Bool := FileMap.mem p fm
def file_count (fm : Files) : Nat := FileMap.cardinal fm
def file_bindings (fm : Files) : List (FilePath.T × File) := FileMap.elements fm
def file_paths (fm : Files) : List FilePath.T := List.map Prod.fst (file_bindings fm)

theorem file_bindings_find : ∀ (fm : Files) (b : FilePath.T × File),
    b ∈ file_bindings fm → find_file b.1 fm = some b.2 := by
  intro fm ⟨k, e⟩ Hin
  exact (FileFacts.find_mapsto_iff fm k e).1 ((FileFacts.elements_mapsto_iff fm k e).2 Hin)

theorem find_file_bindings : ∀ (fm : Files) k e,
    find_file k fm = some e → (k, e) ∈ file_bindings fm := by
  intro fm k e H
  exact (FileFacts.elements_mapsto_iff fm k e).1 ((FileFacts.find_mapsto_iff fm k e).2 H)

-- Rocq: `in_map`, by induction on the membership (core's `List.mem_map_of_mem` goes through `simp`).
private theorem mem_map_of_mem {A B : Type} (f : A → B) :
    ∀ {a : A} {l : List A}, a ∈ l → f a ∈ List.map f l := by
  intro a l H
  induction H with
  | head _ => exact List.Mem.head _
  | tail _ _ IH => exact List.Mem.tail _ IH

-- Rocq: `in_map_iff`, the forward direction, likewise.
private theorem mem_of_mem_map {A B : Type} (f : A → B) :
    ∀ {b : B} {l : List A}, b ∈ List.map f l → ∃ a, a ∈ l ∧ f a = b := by
  intro b l
  induction l with
  | nil => intro H; exact nomatch H
  | cons x xs IH =>
    intro H
    have H' : b ∈ f x :: List.map f xs := H
    cases H' with
    | head => exact ⟨x, List.Mem.head _, rfl⟩
    | tail _ H'' =>
      obtain ⟨a, Ha, Hb⟩ := IH H''
      exact ⟨a, List.Mem.tail _ Ha, Hb⟩

theorem file_bindings_nodup_keys : ∀ fm, List.Nodup (List.map Prod.fst (file_bindings fm)) := by
  intro fm
  unfold file_bindings
  have H := FileMap.elements_3w fm
  revert H
  generalize FileMap.elements fm = l
  intro H
  induction H with
  | nil => exact List.Pairwise.nil
  | @cons p l' Hni _ IH =>
    refine List.Pairwise.cons ?_ IH
    intro k Hk Heq
    obtain ⟨q, Hq, Hkq⟩ := mem_of_mem_map Prod.fst Hk
    exact Hni q Hq (Heq.trans Hkq.symm)

def file_nodes (fm : Files) : List FileNode :=
  List.map (fun b => MakeFileNode b.1 b.2) (file_bindings fm)
def map_file_values {B : Type} (f : File → B) (fm : Files) : FileMap.t B := FileMap.map f fm
def FilesEqual (fm1 fm2 : Files) : Prop := FileMap.Equal fm1 fm2

theorem files_equal_refl : ∀ fm, FilesEqual fm fm := fun _ _ => rfl
theorem files_equal_sym : ∀ fm1 fm2, FilesEqual fm1 fm2 → FilesEqual fm2 fm1 :=
  fun _ _ H p => (H p).symm
theorem files_equal_trans : ∀ fm1 fm2 fm3, FilesEqual fm1 fm2 → FilesEqual fm2 fm3 → FilesEqual fm1 fm3 :=
  fun _ _ _ H12 H23 p => (H12 p).trans (H23 p)

/-- The duplicate-rejecting builder: standard `mem` then `add`, rejecting a repeated path before adding. -/
def files_of_nodes : List FileNode → Option Files
  | [] => some empty_files
  | n :: rest =>
    match files_of_nodes rest with
    | none => none
    | some fm => bif file_mem (path n) fm then none else some (FileMap.add (path n) (source n) fm)

-- The three unfoldings of the `cons` equation that the proofs below case through (Rocq: `simpl`).
private theorem files_of_nodes_cons (n : FileNode) (rest : List FileNode) :
    files_of_nodes (n :: rest) =
      match files_of_nodes rest with
      | none => none
      | some fm => bif file_mem (path n) fm then none else some (FileMap.add (path n) (source n) fm) := rfl

private theorem files_of_nodes_cons_none (n : FileNode) (rest : List FileNode)
    (H : files_of_nodes rest = none) : files_of_nodes (n :: rest) = none := by
  rw [files_of_nodes_cons, H]

private theorem files_of_nodes_cons_mem (n : FileNode) (rest : List FileNode) (fm : Files)
    (H : files_of_nodes rest = some fm) (Hmem : file_mem (path n) fm = true) :
    files_of_nodes (n :: rest) = none := by
  rw [files_of_nodes_cons, H]
  show (bif file_mem (path n) fm then none else some (FileMap.add (path n) (source n) fm)) = none
  rw [Hmem]
  rfl

private theorem files_of_nodes_cons_new (n : FileNode) (rest : List FileNode) (fm : Files)
    (H : files_of_nodes rest = some fm) (Hmem : file_mem (path n) fm = false) :
    files_of_nodes (n :: rest) = some (FileMap.add (path n) (source n) fm) := by
  rw [files_of_nodes_cons, H]
  show (bif file_mem (path n) fm then none else some (FileMap.add (path n) (source n) fm)) = _
  rw [Hmem]
  rfl

theorem files_of_nodes_in : ∀ nodes fm,
    files_of_nodes nodes = some fm →
    ∀ p, FileMap.In p fm ↔ p ∈ List.map path nodes := by
  intro nodes
  induction nodes with
  | nil =>
    intro fm Hbuild p
    have Hfm : empty_files = fm := Option.some.inj Hbuild
    subst Hfm
    constructor
    · intro ⟨sf, Hsf⟩; exact absurd Hsf (FileMap.empty_1 p sf)
    · intro H; exact nomatch H
  | cons n rest IH =>
    intro fm Hbuild p
    cases Erest : files_of_nodes rest with
    | none => rw [files_of_nodes_cons_none n rest Erest] at Hbuild; exact nomatch Hbuild
    | some fm' =>
      cases Emem : file_mem (path n) fm' with
      | true => rw [files_of_nodes_cons_mem n rest fm' Erest Emem] at Hbuild; exact nomatch Hbuild
      | false =>
        rw [files_of_nodes_cons_new n rest fm' Erest Emem] at Hbuild
        have Hfm := Option.some.inj Hbuild
        subst Hfm
        have IH' := IH fm' Erest p
        refine Iff.trans (FileFacts.add_in_iff fm' (path n) p (source n)) ?_
        constructor
        · intro H
          cases H with
          | inl Heq => subst Heq; exact List.Mem.head _
          | inr Hin => exact List.Mem.tail _ (IH'.1 Hin)
        · intro H
          have H' : p ∈ path n :: List.map path rest := H
          cases H' with
          | head => exact Or.inl rfl
          | tail _ H'' => exact Or.inr (IH'.2 H'')

theorem files_of_nodes_success_iff_unique : ∀ nodes,
    (∃ fm, files_of_nodes nodes = some fm) ↔ List.Nodup (List.map path nodes) := by
  intro nodes
  induction nodes with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => ⟨empty_files, rfl⟩⟩
  | cons n rest IH =>
    constructor
    · intro ⟨fm, Hbuild⟩
      cases Erest : files_of_nodes rest with
      | none => rw [files_of_nodes_cons_none n rest Erest] at Hbuild; exact nomatch Hbuild
      | some fm' =>
        cases Emem : file_mem (path n) fm' with
        | true => rw [files_of_nodes_cons_mem n rest fm' Erest Emem] at Hbuild; exact nomatch Hbuild
        | false =>
          show List.Pairwise (fun a b => a ≠ b) (path n :: List.map path rest)
          refine List.Pairwise.cons ?_ (IH.1 ⟨fm', Erest⟩)
          intro q Hq Heq
          subst Heq
          have Hbad : FileMap.In (path n) fm' := (files_of_nodes_in rest fm' Erest (path n)).2 Hq
          have Hm : file_mem (path n) fm' = true := FileMap.mem_1 Hbad
          exact Bool.noConfusion (Hm.symm.trans Emem)
    · intro Hnd
      have Hnd' : List.Pairwise (fun a b => a ≠ b) (path n :: List.map path rest) := Hnd
      cases Hnd' with
      | cons Hni Hnd'' =>
        obtain ⟨fm', Hrest⟩ := IH.2 Hnd''
        cases Emem : file_mem (path n) fm' with
        | true =>
          exfalso
          have Hin : FileMap.In (path n) fm' := FileMap.mem_2 Emem
          exact Hni (path n) ((files_of_nodes_in rest fm' Hrest (path n)).1 Hin) rfl
        | false =>
          exact ⟨FileMap.add (path n) (source n) fm', files_of_nodes_cons_new n rest fm' Hrest Emem⟩

theorem files_of_nodes_none_iff_duplicate : ∀ nodes,
    files_of_nodes nodes = none ↔ ¬ List.Nodup (List.map path nodes) := by
  intro nodes
  constructor
  · intro Hnone Hnd
    obtain ⟨fm, Hfm⟩ := (files_of_nodes_success_iff_unique nodes).2 Hnd
    rw [Hfm] at Hnone
    exact nomatch Hnone
  · intro Hnd
    cases E : files_of_nodes nodes with
    | none => rfl
    | some fm => exact absurd ((files_of_nodes_success_iff_unique nodes).1 ⟨fm, E⟩) Hnd

theorem files_of_nodes_maps_to : ∀ nodes fm,
    files_of_nodes nodes = some fm →
    ∀ n, n ∈ nodes → maps_to_file (path n) (source n) fm := by
  intro nodes
  induction nodes with
  | nil => intro fm _ n Hin; exact nomatch Hin
  | cons h rest IH =>
    intro fm Hbuild n Hin
    cases Erest : files_of_nodes rest with
    | none => rw [files_of_nodes_cons_none h rest Erest] at Hbuild; exact nomatch Hbuild
    | some fm' =>
      cases Emem : file_mem (path h) fm' with
      | true => rw [files_of_nodes_cons_mem h rest fm' Erest Emem] at Hbuild; exact nomatch Hbuild
      | false =>
        rw [files_of_nodes_cons_new h rest fm' Erest Emem] at Hbuild
        have Hfm := Option.some.inj Hbuild
        subst Hfm
        unfold maps_to_file
        cases Hin with
        | head => exact FileMap.add_1 rfl
        | tail _ Hin' =>
          have Hin'' : FileMap.In (path n) fm' :=
            (files_of_nodes_in rest fm' Erest (path n)).2 (mem_map_of_mem path Hin')
          have Hne : path h ≠ path n := fun Heq => by
            have Hm : file_mem (path n) fm' = true := FileMap.mem_1 Hin''
            rw [← Heq] at Hm
            exact Bool.noConfusion (Hm.symm.trans Emem)
          exact FileMap.add_2 Hne (IH fm' Erest n Hin')

theorem files_of_nodes_mapsto_source : ∀ nodes fm,
    files_of_nodes nodes = some fm →
    ∀ p sf, maps_to_file p sf fm → ∃ n, n ∈ nodes ∧ path n = p ∧ source n = sf := by
  intro nodes
  induction nodes with
  | nil =>
    intro fm Hbuild p sf Hmt
    have Hfm : empty_files = fm := Option.some.inj Hbuild
    subst Hfm
    exact absurd Hmt (FileMap.empty_1 p sf)
  | cons h rest IH =>
    intro fm Hbuild p sf Hmt
    cases Erest : files_of_nodes rest with
    | none => rw [files_of_nodes_cons_none h rest Erest] at Hbuild; exact nomatch Hbuild
    | some fm' =>
      cases Emem : file_mem (path h) fm' with
      | true => rw [files_of_nodes_cons_mem h rest fm' Erest Emem] at Hbuild; exact nomatch Hbuild
      | false =>
        rw [files_of_nodes_cons_new h rest fm' Erest Emem] at Hbuild
        have Hfm := Option.some.inj Hbuild
        subst Hfm
        unfold maps_to_file at Hmt
        cases (FileFacts.add_mapsto_iff fm' (path h) p (source h) sf).1 Hmt with
        | inl H => exact ⟨h, List.Mem.head _, H.1, H.2⟩
        | inr H =>
          obtain ⟨n, Hin, Hp, Hsf⟩ := IH fm' Erest p sf H.2
          exact ⟨n, List.Mem.tail _ Hin, Hp, Hsf⟩

theorem files_of_nodes_find : ∀ nodes fm p sf,
    files_of_nodes nodes = some fm →
    (find_file p fm = some sf ↔ ∃ n, n ∈ nodes ∧ path n = p ∧ source n = sf) := by
  intro nodes fm p sf Hbuild
  unfold find_file
  constructor
  · intro Hf
    exact files_of_nodes_mapsto_source nodes fm Hbuild p sf ((FileFacts.find_mapsto_iff fm p sf).2 Hf)
  · intro ⟨n, Hin, Hp, Hsf⟩
    have Hmt := files_of_nodes_maps_to nodes fm Hbuild n Hin
    unfold maps_to_file at Hmt
    rw [Hp, Hsf] at Hmt
    exact (FileFacts.find_mapsto_iff fm p sf).1 Hmt

theorem files_of_nodes_duplicate_rejects : ∀ p sf,
    files_of_nodes [MakeFileNode p sf, MakeFileNode p sf] = none := by
  intro p sf
  apply (files_of_nodes_none_iff_duplicate _).2
  intro Hnd
  have Hnd' : List.Pairwise (fun a b => a ≠ b) [p, p] := Hnd
  cases Hnd' with
  | cons Hni _ => exact Hni p (List.Mem.head _) rfl

theorem files_of_nodes_duplicate_different_source_rejects : ∀ p sf1 sf2,
    files_of_nodes [MakeFileNode p sf1, MakeFileNode p sf2] = none := by
  intro p sf1 sf2
  apply (files_of_nodes_none_iff_duplicate _).2
  intro Hnd
  have Hnd' : List.Pairwise (fun a b => a ≠ b) [p, p] := Hnd
  cases Hnd' with
  | cons Hni _ => exact Hni p (List.Mem.head _) rfl

/-- Permuting the input nodes yields a semantically equal map, so construction order never leaks. -/
theorem files_of_nodes_permutation : ∀ nodes1 nodes2 fm1 fm2,
    List.Perm nodes1 nodes2 →
    files_of_nodes nodes1 = some fm1 → files_of_nodes nodes2 = some fm2 →
    FilesEqual fm1 fm2 := by
  intro nodes1 nodes2 fm1 fm2 Hperm H1 H2 p
  cases E1 : FileMap.find p fm1 with
  | some sf =>
    obtain ⟨n, Hin, Hp, Hs⟩ := (files_of_nodes_find nodes1 fm1 p sf H1).1 E1
    exact ((files_of_nodes_find nodes2 fm2 p sf H2).2 ⟨n, Hperm.mem_iff.1 Hin, Hp, Hs⟩).symm
  | none =>
    cases E2 : FileMap.find p fm2 with
    | none => rfl
    | some sf =>
      exfalso
      obtain ⟨n, Hin, Hp, Hs⟩ := (files_of_nodes_find nodes2 fm2 p sf H2).1 E2
      have Hbad : find_file p fm1 = some sf :=
        (files_of_nodes_find nodes1 fm1 p sf H1).2 ⟨n, Hperm.symm.mem_iff.1 Hin, Hp, Hs⟩
      unfold find_file at Hbad
      rw [E1] at Hbad
      exact nomatch Hbad

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The module spec: intrinsic facts about the generated module, not about its environment. -/
structure ModuleSpec : Type where
  MakeModuleSpec ::
  module_path : ModulePath.T
  module_version : Version.Version

export ModuleSpec (MakeModuleSpec module_path module_version)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Program : Type where
  MakeProgram ::
  module_spec : ModuleSpec
  files : Files

export Program (MakeProgram module_spec files)

def program_bindings (p : Program) : List (FilePath.T × File) := file_bindings (files p)
def program_keys (p : Program) : List FilePath.T := file_paths (files p)
def program_find (path : FilePath.T) (p : Program) : Option File := find_file path (files p)

def main_source (decls : List TopLevelDecl) : File := MakeFile MainPackage [] decls

def main_file_node (path : FilePath.T) (decls : List TopLevelDecl) : FileNode :=
  MakeFileNode path (main_source decls)

def singleton_program (ms : ModuleSpec) (path : FilePath.T) (decls : List TopLevelDecl) : Program :=
  MakeProgram ms (FileMap.add path (main_source decls) empty_files)

/-- A module-only program: a valid `ModuleSpec` with NO source files. -/
def empty_program (ms : ModuleSpec) : Program :=
  MakeProgram ms empty_files

def build_program (ms : ModuleSpec) (nodes : List FileNode) : Option Program :=
  match files_of_nodes nodes with
  | none => none
  | some fm => some (MakeProgram ms fm)

theorem build_program_some_iff_unique : ∀ ms nodes,
    (∃ p, build_program ms nodes = some p) ↔ List.Nodup (List.map path nodes) := by
  intro ms nodes
  refine Iff.trans ?_ (files_of_nodes_success_iff_unique nodes)
  unfold build_program
  constructor
  · intro ⟨p, Hp⟩
    cases E : files_of_nodes nodes with
    | some fm => exact ⟨fm, rfl⟩
    | none => rw [E] at Hp; exact nomatch Hp
  · intro ⟨fm, Hfm⟩
    rw [Hfm]
    exact ⟨MakeProgram ms fm, rfl⟩

end Fido.Syntax
