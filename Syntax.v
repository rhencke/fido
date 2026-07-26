(** Syntax — the ONE raw program representation.  The permanent root pairs an intrinsic module spec with a
    STANDARD `FilePath.T`-keyed finite map of specification-shaped source-file roots (a [Files] =
    [Collections.FileMap.t File], the pinned-stdlib [FMapAVL] over the [FilePath.T] ordered key; it
    MAY be empty):

      Program := { module_spec : ModuleSpec ; files : Files }

    The PATH is the map KEY, so a map binding `FilePath.T -> File` IS the file-root program occurrence;
    the path is NOT stored in the mapped source value.

    [ModuleSpec] describes the GENERATED Go module itself — its import-path prefix ([ModulePath.T]) and its
    module-declared language version ([Version]) — NOT ambient execution details (no GOOS/GOARCH/ABI/
    scheduler/point-release/architecture matrix; those stay operationally pinned, off the theorems).  It
    is NOT a TargetConfig.

    A [File] is the specification-shaped RAW source of one file: a package clause ([MainPackage] only
    today), a (currently empty) import section, and top-level declarations — nothing compiled.  The package
    clause is SOURCE-owned (rendered by Render); package GROUPING, entry status, and types are COMPILATION /
    TYPING RESULTS — grouping and entry status by Admissible, types by Typing (the one type authority) —
    derived over the whole path-keyed source forest.  There is no raw GoPackage tree and no typed AST: raw
    literals stay UNTYPED syntax.  The file's placement PATH is the standard-map KEY (one path authority),
    never a child production inside the source grammar; [FileNode] (path + source) is a construction / view
    value only — the builder input, never the stored map value.

    The one raw declaration today is [Main body]: syntactically a `func main() { body }` declaration
    (zero parameters, no results) whose body is the existing [Println] statements.  Whether that
    declaration is the UNIQUE entry point of its package is decided by Admissible — MULTIPLE [Main] in a
    file are representable precisely so Admissible can reject a duplicate `main` exactly as Go would.  A
    file with NO declarations is representable (a valid file in a package whose `main` is elsewhere), and
    the EMPTY source forest is representable (a valid module with a `go.mod` and no packages).

    No identifiers, calls, parameters, results, non-empty imports, arbitrary expressions/statements, user
    types, concurrency, or non-`main` package clauses.  Anything else is UNREPRESENTABLE. *)
From Stdlib Require Import NArith List String.
From Stdlib Require Import Permutation SetoidList.
From Fido Require Import FilePath Collections ModulePath Version Integer Float Complex Names.
Import ListNotations.

(** A raw expression is UNTYPED syntax: a boolean literal, an integer literal as an unsigned magnitude
    ([IntegerLiteral]) optionally negated ([NegatedIntegerLiteral]), a STRING literal whose argument is the EXACT SEMANTIC BYTE
    SEQUENCE ([StringLiteral], a Rocq [string] = a list of [ascii] bytes — NOT source spelling, NOT an
    already-escaped literal, NOT Unicode scalars/code points), a FLOATING literal carrying an INTRINSIC
    finite-decimal semantic value ([FloatLiteral d], a bounded canonical [Float.Decimal] — NOT source spelling /
    underscores / hex / capitalization / a rounded value), a COMPLEX literal ([ComplexLiteral dc], carrying two
    [Float.Decimal] components — its canonical spelling is Go's predeclared `complex(re, im)` form, NOT
    imaginary-literal syntax and NOT a general call), or an EXPLICIT conversion ([Convert ts e], the source
    spelling `<render ts>(e)`, e.g. `int8(42)` / `uint64(...)` / `float32(e)` / `complex64(e)` / `byte(0)` /
    `rune(...)`).  The conversion TARGET is a SOURCE type-name syntax ([TypeExpr] — one of the sixteen
    supported names from [Names], carrying its retained source [Names.Identifier], NEVER a semantic
    [Integer.Kind] / [Float.Kind] / [Complex.Kind] / [Typing.SemanticType] tag).  Binding that name to a semantic type is
    COMPILER work in [Admissible]; the AST does not decide that `byte` means `uint8` or `rune` means `int32`.
    Nesting is representable syntax that may be compiler-invalid
    (`uint8(int(300))`, `int8(int16(128))`, `int(3.5)`, `float32(true)`, `int(complex(3.5, 0.0))`) — such a
    program is REJECTED by Typing/Admissible, not unrepresentable.  No type is attached here — the exact
    untyped-constant meaning (a bare float denotes its EXACT rational value; a conversion rounds ONCE at the
    destination format) and the context-directed typing/representability of these literals are the concern of
    [Typing]; the canonical source spelling is a separate proved encoding in [Render].  [IntegerLiteral]/[NegatedIntegerLiteral]
    remain exact untyped integer-literal syntax.  No arithmetic, comparison, bitwise, shift, division,
    arbitrary/qualified/user type names, imaginary-literal syntax, `real`/`imag`, NaN/Inf constructors,
    parenthesis node, variables, calls, or string operations are representable. *)

(** the SOURCE type-name syntax of an explicit conversion target.  Only an UNQUALIFIED predeclared name is
    live today ([Unqualified] wraps a [Names.SupportedType] — a retained source identifier + its
    classified sixteen-name symbol); a qualified name would need imports and package binding and is future
    work (deliberately no dead qualified constructor). *)
Inductive TypeName : Type := Unqualified : Names.SupportedType -> TypeName.
Inductive TypeExpr : Type := NamedType : TypeName -> TypeExpr.

(** the retained supported source name, its classified predeclared symbol (source identity only — no semantic
    type), and its source identifier. *)
Definition type_expr_supported  (ts : TypeExpr) : Names.SupportedType :=
  match ts with NamedType (Unqualified stn) => stn end.
Definition type_expr_name (ts : TypeExpr) : Names.TypeName := Names.symbol (type_expr_supported ts).
Definition type_expr_identifier (ts : TypeExpr) : Names.Identifier := Names.identifier (type_expr_supported ts).
(** the smart constructor: the source conversion-target syntax for one of the sixteen supported names. *)
Definition type_expr_of_name (t : Names.TypeName) : TypeExpr := NamedType (Unqualified (Names.supported_of t)).
Lemma type_expr_supported_of  : forall t, type_expr_supported  (type_expr_of_name t) = Names.supported_of t.  Proof. reflexivity. Qed.
Lemma type_expr_name_of : forall t, type_expr_name (type_expr_of_name t) = t.                 Proof. reflexivity. Qed.

Inductive Expr : Type :=
| BoolLiteral           : bool -> Expr
| IntegerLiteral            : N -> Expr
| NegatedIntegerLiteral            : N -> Expr
| StringLiteral         : string -> Expr
| FloatLiteral          : Float.Decimal -> Expr
| ComplexLiteral        : Complex.Decimal -> Expr
| Convert        : TypeExpr -> Expr -> Expr.

Inductive Stmt : Type :=
| Println : list Expr -> Stmt.

(** A raw top-level declaration.  Today: a `func main()` declaration with a statement body. *)
Inductive Decl : Type :=
| Main : list Stmt -> Decl.

(** the SPECIFICATION-SHAPED source file root.  A source file is no longer a
    bare declaration list: it follows the Go specification's abstract source-file structure — a package clause,
    a (currently empty) import section, and top-level declarations ([File]).  The whole program stores
    these in a STANDARD `FilePath.T`-keyed finite map [Files] ([FMapAVL]): the FILE PATH is the MAP KEY (not a
    child production inside the source grammar, and NOT stored in the mapped source value), so a map binding
    `FilePath.T -> File` IS the file-root program occurrence.  [FileNode] (path + source) is a
    CONSTRUCTION / derived-VIEW value only — the input to the duplicate-rejecting builder, never the stored map
    value.

    The LIVE domains are intentionally narrow but shaped as the PERMANENT categories (Master Plan 3.2): the
    package clause is only the canonical `package main` ([MainPackage]); imports are INTRINSICALLY empty
    ([ImportSpec] has no constructors, so [list ImportSpec] can only be [nil]); top-level
    declarations are the current [Decl] form.  This avoids the subset-filter mistake (representing arbitrary
    packages/imports and then rejecting them). *)

(** The package clause as source syntax — only the canonical `package main` is representable today. *)
Inductive PackageClause : Type := MainPackage.

(** An import spec — NO import is representable yet, so the type is EMPTY and [list ImportSpec] = [nil]. *)
Inductive ImportSpec : Type := .

(** A top-level declaration as source syntax — the current [Decl] form (`func main()` today). *)
Definition TopLevelDecl := Decl.

(** One source file's abstract structure (package clause + imports + top-level declarations, in order).
    A declaration list REMAINS — as the [declarations] field — but is no longer the entire file. *)
Record File : Type := make_file {
  package : PackageClause;
  imports : list ImportSpec;
  declarations   : list TopLevelDecl
}.

(** A CONSTRUCTION / VIEW value pairing a placement path with its source — the input to the duplicate-rejecting
    builder and a derived view of a map binding, NEVER the stored map value.  The ONE path authority is the
    [Files] KEY (below), not this node's [path] field. *)
Record FileNode : Type := make_file_node {
  path   : FilePath.T;
  source : File
}.

(** ----: the path-keyed source forest is a STANDARD finite map (FilePath.T -> File).  The path is
    the map KEY (the ONE path authority), NOT stored in the mapped value; [FileNode] is a construction/view
    value only.  Backed by [Collections.FileMap] (the pinned-stdlib AVL map) — Fido authors no map. ---- *)

Module FileMap := Collections.FileMap.
Module FileFacts := Collections.FileFacts.

Definition Files : Type := FileMap.t File.

Definition empty_files : Files := FileMap.empty File.
Definition find_file (p : FilePath.T) (fm : Files) : option File := FileMap.find p fm.
Definition maps_to_file (p : FilePath.T) (sf : File) (fm : Files) : Prop := FileMap.MapsTo p sf fm.
Definition file_mem (p : FilePath.T) (fm : Files) : bool := FileMap.mem p fm.
Definition file_count (fm : Files) : nat := FileMap.cardinal fm.
(** DERIVED canonical (FilePath.T-ordered) enumerations — never a second semantic authority. *)
Definition file_bindings (fm : Files) : list (FilePath.T * File) := FileMap.elements fm.
Definition file_paths (fm : Files) : list FilePath.T := List.map fst (file_bindings fm).
(** Each canonical binding's key maps to its value (the standard [elements]->[find] bridge, used by an
    indexed whole-program traversal to mint a file reference per binding). *)
Lemma file_bindings_find : forall (fm : Files) (b : FilePath.T * File),
  List.In b (file_bindings fm) -> find_file (fst b) fm = Some (snd b).
Proof.
  intros fm [k e] Hin. unfold file_bindings, find_file in *. simpl in *.
  apply FileFacts.find_mapsto_iff, FileFacts.elements_mapsto_iff, SetoidList.InA_alt.
  exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

(** the dual: a key that [find]s a value occurs as that binding in the canonical enumeration (used to build a
    package anchor from a validated file reference). *)
Lemma find_file_bindings : forall (fm : Files) k e,
  find_file k fm = Some e -> List.In (k, e) (file_bindings fm).
Proof.
  intros fm k e H. unfold file_bindings, find_file in *.
  apply FileFacts.find_mapsto_iff, FileFacts.elements_mapsto_iff, SetoidList.InA_alt in H.
  destruct H as [[k' e'] [[Hk He] Hin]]. cbn in Hk, He.
  unfold Collections.FilePathOrder.eq in Hk. subst. exact Hin.
Qed.

(** the canonical enumeration has DISTINCT keys (the map's keys are unique) — used to prove program-wide
    occurrence keys are distinct across files. *)
Lemma file_bindings_nodup_keys : forall fm, List.NoDup (List.map fst (file_bindings fm)).
Proof.
  intro fm. unfold file_bindings. pose proof (FileMap.elements_3w fm) as H.
  generalize dependent (FileMap.elements fm). clear fm. intro l.
  induction l as [|[k e] l IH]; simpl; intro H; [constructor|].
  inversion H as [|x xs Hni Hnd Heq]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' e'] [Hk Hin']]. cbn in Hk; subst k'.
    apply Hni, SetoidList.InA_alt. exists (k, e'). split; [ reflexivity | exact Hin' ].
  - apply IH; exact Hnd.
Qed.
Definition file_nodes (fm : Files) : list FileNode :=
  List.map (fun b => make_file_node (fst b) (snd b)) (file_bindings fm).
Definition map_file_values {B} (f : File -> B) (fm : Files) : FileMap.t B := FileMap.map f fm.
(** SEMANTIC file-map equality — the standard map [Equal]. *)
Definition FilesEqual (fm1 fm2 : Files) : Prop := FileMap.Equal fm1 fm2.

Lemma FilesEqual_refl : forall fm, FilesEqual fm fm.
Proof. intros fm p. reflexivity. Qed.
Lemma FilesEqual_sym : forall fm1 fm2, FilesEqual fm1 fm2 -> FilesEqual fm2 fm1.
Proof. intros fm1 fm2 H p. symmetry. apply H. Qed.
Lemma FilesEqual_trans : forall fm1 fm2 fm3, FilesEqual fm1 fm2 -> FilesEqual fm2 fm3 -> FilesEqual fm1 fm3.
Proof. intros fm1 fm2 fm3 H12 H23 p. rewrite H12. apply H23. Qed.

(** ---- the duplicate-rejecting map builder: standard [mem]/[add], reject a duplicate path before add. ---- *)

Fixpoint files_of_nodes (nodes : list FileNode) : option Files :=
  match nodes with
  | [] => Some empty_files
  | n :: rest =>
      match files_of_nodes rest with
      | None => None
      | Some fm => if file_mem (path n) fm then None
                   else Some (FileMap.add (path n) (source n) fm)
      end
  end.

(** the key domain of a successfully built map is exactly the input node paths. *)
Lemma files_of_nodes_in : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall p, FileMap.In p fm <-> In p (List.map path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl; intros fm Hbuild p.
  - injection Hbuild as <-. split.
    + intros [sf Hsf]. exfalso. apply (FileMap.empty_1 (elt:=File) Hsf).
    + intros [].
  - destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (path n) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. specialize (IH fm' eq_refl).
    rewrite FileFacts.add_in_iff, IH. split.
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
Qed.

(** SUCCESS iff the input paths are duplicate-free. *)
Theorem files_of_nodes_success_iff_unique : forall nodes,
  (exists fm, files_of_nodes nodes = Some fm) <-> NoDup (List.map path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl.
  - split; [ intros _; constructor | intros _; eexists; reflexivity ].
  - split.
    + intros [fm Hbuild]. destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
      destruct (file_mem (path n) fm') eqn:Emem; [ discriminate | ].
      constructor.
      * intro Hin. assert (Hbad : FileMap.In (path n) fm').
        { apply (files_of_nodes_in rest fm' Erest). exact Hin. }
        apply FileMap.mem_1 in Hbad. unfold file_mem in Emem. rewrite Hbad in Emem. discriminate.
      * apply IH. exists fm'; reflexivity.
    + intro Hnd. inversion Hnd as [ | h t Hni Hnd' ]; subst.
      destruct (proj2 IH Hnd') as [fm' Hrest]. rewrite Hrest.
      destruct (file_mem (path n) fm') eqn:Emem.
      * exfalso. unfold file_mem in Emem. apply FileMap.mem_2 in Emem.
        apply (files_of_nodes_in rest fm' Hrest) in Emem. contradiction.
      * eexists; reflexivity.
Qed.

(** NONE iff a duplicate path. *)
Theorem files_of_nodes_none_iff_duplicate : forall nodes,
  files_of_nodes nodes = None <-> ~ NoDup (List.map path nodes).
Proof.
  intro nodes. split.
  - intros Hnone Hnd. destruct (proj2 (files_of_nodes_success_iff_unique nodes) Hnd) as [fm Hfm].
    rewrite Hfm in Hnone. discriminate.
  - intro Hnd. destruct (files_of_nodes nodes) as [fm|] eqn:E; [ | reflexivity ].
    exfalso. apply Hnd. apply (files_of_nodes_success_iff_unique nodes). eexists; exact E.
Qed.

(** POSITIVE EXACTNESS: on success, EVERY input node's path maps to ITS OWN source — the builder
    actually populates each binding; because it rejects a duplicate before adding, no source is ever silently
    overwritten (a later same-path node makes the build FAIL, it does not clobber the earlier binding). *)
Lemma files_of_nodes_maps_to : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall n, In n nodes -> maps_to_file (path n) (source n) fm.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild n Hin; [ contradiction | ].
  destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
  destruct (file_mem (path h) fm') eqn:Emem; [ discriminate | ].
  injection Hbuild as <-. unfold maps_to_file. destruct Hin as [ -> | Hin ].
  - apply FileMap.add_1. reflexivity.
  - assert (Hin' : FileMap.In (path n) fm')
      by (apply (files_of_nodes_in rest fm' Erest); apply in_map; exact Hin).
    assert (Hne : path h <> path n).
    { intro Heq. rewrite Heq in Emem. apply FileMap.mem_1 in Hin'. unfold file_mem in Emem.
      rewrite Hin' in Emem. discriminate. }
    apply FileMap.add_2; [ exact Hne | apply (IH fm' eq_refl n Hin) ].
Qed.

(** REVERSE EXACTNESS: every binding of the built map comes from an input node — the map invents no
    binding.  Together with [files_of_nodes_maps_to] this pins the built map EXACTLY to the input forest. *)
Lemma files_of_nodes_mapsto_source : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall p sf, maps_to_file p sf fm -> exists n, In n nodes /\ path n = p /\ source n = sf.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild p sf Hmt.
  - injection Hbuild as <-. unfold maps_to_file in Hmt. exfalso. apply (FileMap.empty_1 Hmt).
  - destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (path h) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. unfold maps_to_file in Hmt.
    apply FileFacts.add_mapsto_iff in Hmt. destruct Hmt as [ [Heq Hsf] | [Hne Hmt'] ].
    + exists h. split; [ left; reflexivity | split; [ exact Heq | exact Hsf ] ].
    + destruct (IH fm' eq_refl p sf Hmt') as [ n [Hin [Hp Hsf]] ].
      exists n. split; [ right; exact Hin | split; [ exact Hp | exact Hsf ] ].
Qed.

(** the FULL find-characterization (both exactness directions in one iff): a key maps to a source in the built
    map IFF some input node carries exactly that path and source. *)
Lemma files_of_nodes_find : forall nodes fm p sf,
  files_of_nodes nodes = Some fm ->
  (find_file p fm = Some sf <-> exists n, In n nodes /\ path n = p /\ source n = sf).
Proof.
  intros nodes fm p sf Hbuild. unfold find_file. split.
  - intro Hf. apply FileFacts.find_mapsto_iff in Hf. exact (files_of_nodes_mapsto_source nodes fm Hbuild p sf Hf).
  - intros [n [Hin [Hp Hsf]]]. apply FileFacts.find_mapsto_iff.
    pose proof (files_of_nodes_maps_to nodes fm Hbuild n Hin) as Hmt.
    unfold maps_to_file in Hmt. rewrite Hp, Hsf in Hmt. exact Hmt.
Qed.

(** a repeated path REJECTS the build whether the two sources are EQUAL … *)
Lemma files_of_nodes_duplicate_rejects : forall p sf,
  files_of_nodes (make_file_node p sf :: make_file_node p sf :: nil) = None.
Proof.
  intros p sf. apply files_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

(** … or DIFFER — the standard-map overwrite never silently erases the earlier source. *)
Lemma files_of_nodes_duplicate_different_source_rejects : forall p sf1 sf2,
  files_of_nodes (make_file_node p sf1 :: make_file_node p sf2 :: nil) = None.
Proof.
  intros p sf1 sf2. apply files_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

(** ORDER-INDEPENDENCE: permuting the input nodes yields a SEMANTICALLY EQUAL map ([FilesEqual], not
    record [=]) — construction order never leaks into the source forest. *)
Lemma files_of_nodes_permutation : forall nodes1 nodes2 fm1 fm2,
  Permutation nodes1 nodes2 ->
  files_of_nodes nodes1 = Some fm1 -> files_of_nodes nodes2 = Some fm2 ->
  FilesEqual fm1 fm2.
Proof.
  intros nodes1 nodes2 fm1 fm2 Hperm H1 H2 p.
  destruct (FileMap.find p fm1) as [sf|] eqn:E1.
  - apply (files_of_nodes_find nodes1 fm1 p sf H1) in E1. destruct E1 as [n [Hin [Hp Hs]]].
    symmetry. apply (files_of_nodes_find nodes2 fm2 p sf H2).
    exists n. split; [ apply (Permutation_in _ Hperm); exact Hin | split; [ exact Hp | exact Hs ] ].
  - destruct (FileMap.find p fm2) as [sf|] eqn:E2; [ | reflexivity ].
    exfalso. apply (files_of_nodes_find nodes2 fm2 p sf H2) in E2. destruct E2 as [n [Hin [Hp Hs]]].
    assert (Hbad : find_file p fm1 = Some sf).
    { apply (files_of_nodes_find nodes1 fm1 p sf H1).
      exists n. split; [ apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin
                       | split; [ exact Hp | exact Hs ] ]. }
    unfold find_file in Hbad. rewrite E1 in Hbad. discriminate.
Qed.


(** ---- the module spec: intrinsic facts about the GENERATED module (not environment config) ---- *)

Record ModuleSpec : Type := make_module_spec {
  module_path       : ModulePath.T;
  module_version : Version
}.

(** ---- the program: a module spec + a (possibly empty) standard `FilePath.T`-keyed source map ([Files]) ---- *)

Record Program : Type := make_program {
  module_spec : ModuleSpec;
  files  : Files
}.

(** the canonical (FilePath.T-ordered) DERIVED enumeration of (path, source) bindings — used by the executable
    checkers only; [files] (the map) remains the ONE file authority (typing quantifies over [MapsTo]). *)
Definition program_bindings (p : Program) : list (FilePath.T * File) := file_bindings (files p).
Definition program_keys (p : Program) : list FilePath.T := file_paths (files p).
Definition program_find (path : FilePath.T) (p : Program) : option File := find_file path (files p).

(** ---- builders (the source forest MAY be empty) ---- *)

(** the canonical `package main` source file holding a declaration list (a CONVENIENCE that creates ordinary
    source syntax — the renderer never synthesizes source behind the AST's back). *)
Definition main_source (decls : list Decl) : File := make_file MainPackage [] decls.

(** the canonical `package main` file ROOT at a path (convenience node builder). *)
Definition main_file_node (path : FilePath.T) (decls : list Decl) : FileNode :=
  make_file_node path (main_source decls).

(** A single-file program under a module spec. *)
Definition singleton_program (ms : ModuleSpec) (path : FilePath.T) (decls : list Decl) : Program :=
  make_program ms (FileMap.add path (main_source decls) empty_files).

(** A module-only program: a valid [ModuleSpec] with NO source files. *)
Definition empty_program (ms : ModuleSpec) : Program :=
  make_program ms empty_files.

(** The construction API (Master Plan 3.5): from a module spec + a list of specification-shaped file roots,
    [None] ONLY when the collection cannot describe one source tree (chiefly duplicate paths); the EMPTY list
    yields a valid module-only program.  Semantic invalidity remains a compiler result. *)
Definition build_program (ms : ModuleSpec) (nodes : list FileNode) : option Program :=
  match files_of_nodes nodes with
  | None => None
  | Some fm => Some (make_program ms fm)
  end.

(** [build_program] is EXACT over the duplicate-rejecting builder: it succeeds IFF the file paths are unique
    (it fails ONLY on a duplicate path). *)
Theorem build_program_some_iff_unique : forall ms nodes,
  (exists p, build_program ms nodes = Some p) <-> NoDup (List.map path nodes).
Proof.
  intros ms nodes. unfold build_program. rewrite <- files_of_nodes_success_iff_unique. split.
  - intros [p Hp]. destruct (files_of_nodes nodes) as [fm|] eqn:E; [ eexists; reflexivity | discriminate ].
  - intros [fm Hfm]. rewrite Hfm. eexists; reflexivity.
Qed.
