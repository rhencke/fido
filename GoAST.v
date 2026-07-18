(** ============================================================================
    GoAST — the ONE raw program representation.  The permanent root pairs an intrinsic module spec with a
    STANDARD `FilePath`-keyed finite map of specification-shaped source-file roots (a [GoFileMap] =
    [Collections.FileMapBase.t GoSourceFile], the pinned-stdlib [FMapAVL] over the [FilePath] ordered key; it
    MAY be empty):

      GoProgram := { prog_module : ModuleSpec ; prog_files : GoFileMap }

    The PATH is the map KEY, so a map binding `FilePath -> GoSourceFile` IS the file-root program occurrence;
    the path is NOT stored in the mapped source value.

    [ModuleSpec] describes the GENERATED Go module itself — its import-path prefix ([ModulePath]) and its
    module-declared language version ([GoVersion]) — NOT ambient execution details (no GOOS/GOARCH/ABI/
    scheduler/point-release/architecture matrix; those stay operationally pinned, off the theorems).  It
    is NOT a TargetConfig.

    A [GoSourceFile] is the specification-shaped RAW source of one file: a package clause ([PkgMain] only
    today), a (currently empty) import section, and top-level declarations — nothing compiled.  The package
    clause is SOURCE-owned (rendered by GoRender); package GROUPING, entry status, and types are COMPILATION /
    TYPING RESULTS — grouping and entry status by GoCompile, types by GoTypes (the one type authority) —
    derived over the whole path-keyed source forest.  There is no raw GoPackage tree and no typed AST: raw
    literals stay UNTYPED syntax.  The file's placement PATH is the standard-map KEY (one path authority),
    never a child production inside the source grammar; [GoFileNode] (path + source) is a construction / view
    value only — the builder input, never the stored map value.

    The one raw declaration today is [DMain body]: syntactically a `func main() { body }` declaration
    (zero parameters, no results) whose body is the existing [SPrintln] statements.  Whether that
    declaration is the UNIQUE entry point of its package is decided by GoCompile — MULTIPLE [DMain] in a
    file are representable precisely so GoCompile can reject a duplicate `main` exactly as Go would.  A
    file with NO declarations is representable (a valid file in a package whose `main` is elsewhere), and
    the EMPTY source forest is representable (a valid module with a `go.mod` and no packages).

    No identifiers, calls, parameters, results, non-empty imports, arbitrary expressions/statements, user
    types, concurrency, or non-`main` package clauses.  Anything else is UNREPRESENTABLE.
    ============================================================================ *)
From Stdlib Require Import NArith List String.
From Stdlib Require Import Permutation SetoidList.
From Fido Require Import FilePath Collections ModulePath GoVersion Ints Floats Complexes.
Import ListNotations.

(** A raw expression is UNTYPED syntax: a boolean literal, an integer literal as an unsigned magnitude
    ([EInt]) optionally negated ([ENeg]), a STRING literal whose argument is the EXACT SEMANTIC BYTE
    SEQUENCE ([EString], a Rocq [string] = a list of [ascii] bytes — NOT source spelling, NOT an
    already-escaped literal, NOT Unicode scalars/code points), or an EXPLICIT integer conversion
    ([EIntConvert it e], the source spelling `<keyword it>(e)`, e.g. `int8(42)` / `uint64(...)` /
    `uint8(int(300))`), a FLOATING literal carrying an INTRINSIC finite-decimal semantic value ([EFloat d],
    a bounded canonical [DecimalFloat] — NOT source spelling / underscores / hex / capitalization / a rounded
    value), or an EXPLICIT float conversion ([EFloatConvert ft e], the source spelling `float32(e)` /
    `float64(e)`).  [EIntConvert]'s target is the INTRINSIC [IntegerType] and [EFloatConvert]'s the intrinsic
    [FloatType] — never a raw type-name string.  A COMPLEX literal ([EComplex dc], carrying two
    [DecimalFloat] components — its canonical spelling is Go's predeclared `complex(re, im)` form, NOT
    imaginary-literal syntax and NOT a general call), or an EXPLICIT complex conversion ([EComplexConvert ct
    e], the source spelling `complex64(e)` / `complex128(e)`).  [EComplexConvert]'s target is the intrinsic
    [ComplexType].  Nesting is representable syntax that may be compiler-invalid
    (`uint8(int(300))`, `int8(int16(128))`, `int(3.5)`, `float32(true)`, `int(complex(3.5, 0.0))`) — such a
    program is REJECTED by GoTypes/GoCompile, not unrepresentable.  No type is attached here — the exact
    untyped-constant meaning (a bare float denotes its EXACT rational value; a conversion rounds ONCE at the
    destination format) and the context-directed typing/representability of these literals are the concern of
    [GoTypes]; the canonical source spelling is a separate proved encoding in [GoRender].  [EInt]/[ENeg]
    remain exact untyped integer-literal syntax.  No arithmetic, comparison, bitwise, shift, division,
    general named conversion, imaginary-literal syntax, `real`/`imag`, NaN/Inf constructors, parenthesis
    node, variables, calls, or string operations are representable. *)
Inductive GoExpr : Type :=
| EBool           : bool -> GoExpr
| EInt            : N -> GoExpr
| ENeg            : N -> GoExpr
| EString         : string -> GoExpr
| EIntConvert     : IntegerType -> GoExpr -> GoExpr
| EFloat          : DecimalFloat -> GoExpr
| EFloatConvert   : FloatType -> GoExpr -> GoExpr
| EComplex        : DecimalComplex -> GoExpr
| EComplexConvert : ComplexType -> GoExpr -> GoExpr.

Inductive GoStmt : Type :=
| SPrintln : list GoExpr -> GoStmt.

(** A raw top-level declaration.  Today: a `func main()` declaration with a statement body. *)
Inductive GoDecl : Type :=
| DMain : list GoStmt -> GoDecl.

(** ============================================================================
    C1/C1A — the SPECIFICATION-SHAPED source file root (Master Plan 3.1–3.4).  A source file is no longer a
    bare declaration list: it follows the Go specification's abstract source-file structure — a package clause,
    a (currently empty) import section, and top-level declarations ([GoSourceFile]).  The whole program stores
    these in a STANDARD `FilePath`-keyed finite map [GoFileMap] ([FMapAVL]): the FILE PATH is the MAP KEY (not a
    child production inside the source grammar, and NOT stored in the mapped source value), so a map binding
    `FilePath -> GoSourceFile` IS the file-root program occurrence.  [GoFileNode] (path + source) is a
    CONSTRUCTION / derived-VIEW value only — the input to the duplicate-rejecting builder, never the stored map
    value.

    The LIVE domains are intentionally narrow but shaped as the PERMANENT categories (Master Plan 3.2): the
    package clause is only the canonical `package main` ([PkgMain]); imports are INTRINSICALLY empty
    ([ImportSpecSyntax] has no constructors, so [list ImportSpecSyntax] can only be [nil]); top-level
    declarations are the current [GoDecl] form.  This avoids the subset-filter mistake (representing arbitrary
    packages/imports and then rejecting them). ============================================================ *)

(** The package clause as source syntax — only the canonical `package main` is representable today. *)
Inductive PackageClauseSyntax : Type := PkgMain.

(** An import spec — NO import is representable yet, so the type is EMPTY and [list ImportSpecSyntax] = [nil]. *)
Inductive ImportSpecSyntax : Type := .

(** A top-level declaration as source syntax — the current [GoDecl] form (`func main()` today). *)
Definition TopLevelDeclSyntax := GoDecl.

(** One source file's abstract structure (package clause + imports + top-level declarations, in order).
    A declaration list REMAINS — as the [source_decls] field — but is no longer the entire file. *)
Record GoSourceFile : Type := mkSourceFile {
  source_package : PackageClauseSyntax;
  source_imports : list ImportSpecSyntax;
  source_decls   : list TopLevelDeclSyntax
}.

(** A CONSTRUCTION / VIEW value pairing a placement path with its source — the input to the duplicate-rejecting
    builder and a derived view of a map binding, NEVER the stored map value.  The ONE path authority is the
    [GoFileMap] KEY (below), not this node's [file_path] field. *)
Record GoFileNode : Type := mkFileNode {
  file_path   : FilePath;
  file_source : GoSourceFile
}.

(** ---- C1A: the path-keyed source forest is a STANDARD finite map (FilePath -> GoSourceFile).  The path is
    the map KEY (the ONE path authority), NOT stored in the mapped value; [GoFileNode] is a construction/view
    value only.  Backed by [Collections.FileMapBase] (the pinned-stdlib AVL map) — Fido authors no map. ---- *)

Module FM := Collections.FileMapBase.
Module FMF := Collections.FileMapFacts.

Definition GoFileMap : Type := FM.t GoSourceFile.

Definition empty_files : GoFileMap := FM.empty GoSourceFile.
Definition find_file (p : FilePath) (fm : GoFileMap) : option GoSourceFile := FM.find p fm.
Definition maps_to_file (p : FilePath) (sf : GoSourceFile) (fm : GoFileMap) : Prop := FM.MapsTo p sf fm.
Definition file_mem (p : FilePath) (fm : GoFileMap) : bool := FM.mem p fm.
Definition file_count (fm : GoFileMap) : nat := FM.cardinal fm.
(** DERIVED canonical (FilePath-ordered) enumerations — never a second semantic authority. *)
Definition file_bindings (fm : GoFileMap) : list (FilePath * GoSourceFile) := FM.elements fm.
Definition file_paths (fm : GoFileMap) : list FilePath := List.map fst (file_bindings fm).
(** Each canonical binding's key maps to its value (the standard [elements]->[find] bridge, used by an
    indexed whole-program traversal to mint a file reference per binding). *)
Lemma file_bindings_find : forall (fm : GoFileMap) (b : FilePath * GoSourceFile),
  List.In b (file_bindings fm) -> find_file (fst b) fm = Some (snd b).
Proof.
  intros fm [k e] Hin. unfold file_bindings, find_file in *. simpl in *.
  apply FMF.find_mapsto_iff, FMF.elements_mapsto_iff, SetoidList.InA_alt.
  exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

(** the dual: a key that [find]s a value occurs as that binding in the canonical enumeration (used to build a
    package anchor from a validated file reference). *)
Lemma find_file_bindings : forall (fm : GoFileMap) k e,
  find_file k fm = Some e -> List.In (k, e) (file_bindings fm).
Proof.
  intros fm k e H. unfold file_bindings, find_file in *.
  apply FMF.find_mapsto_iff, FMF.elements_mapsto_iff, SetoidList.InA_alt in H.
  destruct H as [[k' e'] [[Hk He] Hin]]. cbn in Hk, He.
  unfold Collections.FilePath_OT.eq in Hk. subst. exact Hin.
Qed.

(** the canonical enumeration has DISTINCT keys (the map's keys are unique) — used to prove program-wide
    occurrence keys are distinct across files. *)
Lemma file_bindings_nodup_keys : forall fm, List.NoDup (List.map fst (file_bindings fm)).
Proof.
  intro fm. unfold file_bindings. pose proof (FM.elements_3w fm) as H.
  generalize dependent (FM.elements fm). clear fm. intro l.
  induction l as [|[k e] l IH]; simpl; intro H; [constructor|].
  inversion H as [|x xs Hni Hnd Heq]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' e'] [Hk Hin']]. cbn in Hk; subst k'.
    apply Hni, SetoidList.InA_alt. exists (k, e'). split; [ reflexivity | exact Hin' ].
  - apply IH; exact Hnd.
Qed.
Definition file_nodes (fm : GoFileMap) : list GoFileNode :=
  List.map (fun b => mkFileNode (fst b) (snd b)) (file_bindings fm).
Definition map_file_values {B} (f : GoSourceFile -> B) (fm : GoFileMap) : FM.t B := FM.map f fm.
(** SEMANTIC file-map equality — the standard map [Equal]. *)
Definition FilesEqual (fm1 fm2 : GoFileMap) : Prop := FM.Equal fm1 fm2.

Lemma FilesEqual_refl : forall fm, FilesEqual fm fm.
Proof. intros fm p. reflexivity. Qed.
Lemma FilesEqual_sym : forall fm1 fm2, FilesEqual fm1 fm2 -> FilesEqual fm2 fm1.
Proof. intros fm1 fm2 H p. symmetry. apply H. Qed.
Lemma FilesEqual_trans : forall fm1 fm2 fm3, FilesEqual fm1 fm2 -> FilesEqual fm2 fm3 -> FilesEqual fm1 fm3.
Proof. intros fm1 fm2 fm3 H12 H23 p. rewrite H12. apply H23. Qed.

(** ---- §6 the duplicate-rejecting map builder: standard [mem]/[add], reject a duplicate path before add. ---- *)

Fixpoint filemap_of_nodes (nodes : list GoFileNode) : option GoFileMap :=
  match nodes with
  | [] => Some empty_files
  | n :: rest =>
      match filemap_of_nodes rest with
      | None => None
      | Some fm => if file_mem (file_path n) fm then None
                   else Some (FM.add (file_path n) (file_source n) fm)
      end
  end.

(** the key domain of a successfully built map is exactly the input node paths. *)
Lemma filemap_of_nodes_in : forall nodes fm,
  filemap_of_nodes nodes = Some fm ->
  forall p, FM.In p fm <-> In p (List.map file_path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl; intros fm Hbuild p.
  - injection Hbuild as <-. split.
    + intros [sf Hsf]. exfalso. apply (FM.empty_1 (elt:=GoSourceFile) Hsf).
    + intros [].
  - destruct (filemap_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (file_path n) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. specialize (IH fm' eq_refl).
    rewrite FMF.add_in_iff, IH. split.
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
Qed.

(** SUCCESS iff the input paths are duplicate-free. *)
Theorem filemap_of_nodes_success_iff_unique : forall nodes,
  (exists fm, filemap_of_nodes nodes = Some fm) <-> NoDup (List.map file_path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl.
  - split; [ intros _; constructor | intros _; eexists; reflexivity ].
  - split.
    + intros [fm Hbuild]. destruct (filemap_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
      destruct (file_mem (file_path n) fm') eqn:Emem; [ discriminate | ].
      constructor.
      * intro Hin. assert (Hbad : FM.In (file_path n) fm').
        { apply (filemap_of_nodes_in rest fm' Erest). exact Hin. }
        apply FM.mem_1 in Hbad. unfold file_mem in Emem. rewrite Hbad in Emem. discriminate.
      * apply IH. exists fm'; reflexivity.
    + intro Hnd. inversion Hnd as [ | h t Hni Hnd' ]; subst.
      destruct (proj2 IH Hnd') as [fm' Hrest]. rewrite Hrest.
      destruct (file_mem (file_path n) fm') eqn:Emem.
      * exfalso. unfold file_mem in Emem. apply FM.mem_2 in Emem.
        apply (filemap_of_nodes_in rest fm' Hrest) in Emem. contradiction.
      * eexists; reflexivity.
Qed.

(** NONE iff a duplicate path. *)
Theorem filemap_of_nodes_none_iff_duplicate : forall nodes,
  filemap_of_nodes nodes = None <-> ~ NoDup (List.map file_path nodes).
Proof.
  intro nodes. split.
  - intros Hnone Hnd. destruct (proj2 (filemap_of_nodes_success_iff_unique nodes) Hnd) as [fm Hfm].
    rewrite Hfm in Hnone. discriminate.
  - intro Hnd. destruct (filemap_of_nodes nodes) as [fm|] eqn:E; [ | reflexivity ].
    exfalso. apply Hnd. apply (filemap_of_nodes_success_iff_unique nodes). eexists; exact E.
Qed.

(** POSITIVE EXACTNESS (§6): on success, EVERY input node's path maps to ITS OWN source — the builder
    actually populates each binding; because it rejects a duplicate before adding, no source is ever silently
    overwritten (a later same-path node makes the build FAIL, it does not clobber the earlier binding). *)
Lemma filemap_of_nodes_maps_to : forall nodes fm,
  filemap_of_nodes nodes = Some fm ->
  forall n, In n nodes -> maps_to_file (file_path n) (file_source n) fm.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild n Hin; [ contradiction | ].
  destruct (filemap_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
  destruct (file_mem (file_path h) fm') eqn:Emem; [ discriminate | ].
  injection Hbuild as <-. unfold maps_to_file. destruct Hin as [ -> | Hin ].
  - apply FM.add_1. reflexivity.
  - assert (Hin' : FM.In (file_path n) fm')
      by (apply (filemap_of_nodes_in rest fm' Erest); apply in_map; exact Hin).
    assert (Hne : file_path h <> file_path n).
    { intro Heq. rewrite Heq in Emem. apply FM.mem_1 in Hin'. unfold file_mem in Emem.
      rewrite Hin' in Emem. discriminate. }
    apply FM.add_2; [ exact Hne | apply (IH fm' eq_refl n Hin) ].
Qed.

(** REVERSE EXACTNESS (§6): every binding of the built map comes from an input node — the map invents no
    binding.  Together with [filemap_of_nodes_maps_to] this pins the built map EXACTLY to the input forest. *)
Lemma filemap_of_nodes_mapsto_source : forall nodes fm,
  filemap_of_nodes nodes = Some fm ->
  forall p sf, maps_to_file p sf fm -> exists n, In n nodes /\ file_path n = p /\ file_source n = sf.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild p sf Hmt.
  - injection Hbuild as <-. unfold maps_to_file in Hmt. exfalso. apply (FM.empty_1 Hmt).
  - destruct (filemap_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (file_path h) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. unfold maps_to_file in Hmt.
    apply FMF.add_mapsto_iff in Hmt. destruct Hmt as [ [Heq Hsf] | [Hne Hmt'] ].
    + exists h. split; [ left; reflexivity | split; [ exact Heq | exact Hsf ] ].
    + destruct (IH fm' eq_refl p sf Hmt') as [ n [Hin [Hp Hsf]] ].
      exists n. split; [ right; exact Hin | split; [ exact Hp | exact Hsf ] ].
Qed.

(** the FULL find-characterization (both exactness directions in one iff): a key maps to a source in the built
    map IFF some input node carries exactly that path and source. *)
Lemma filemap_of_nodes_find : forall nodes fm p sf,
  filemap_of_nodes nodes = Some fm ->
  (find_file p fm = Some sf <-> exists n, In n nodes /\ file_path n = p /\ file_source n = sf).
Proof.
  intros nodes fm p sf Hbuild. unfold find_file. split.
  - intro Hf. apply FMF.find_mapsto_iff in Hf. exact (filemap_of_nodes_mapsto_source nodes fm Hbuild p sf Hf).
  - intros [n [Hin [Hp Hsf]]]. apply FMF.find_mapsto_iff.
    pose proof (filemap_of_nodes_maps_to nodes fm Hbuild n Hin) as Hmt.
    unfold maps_to_file in Hmt. rewrite Hp, Hsf in Hmt. exact Hmt.
Qed.

(** a repeated path REJECTS the build whether the two sources are EQUAL … *)
Lemma filemap_of_nodes_duplicate_rejects : forall p sf,
  filemap_of_nodes (mkFileNode p sf :: mkFileNode p sf :: nil) = None.
Proof.
  intros p sf. apply filemap_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

(** … or DIFFER — the standard-map overwrite never silently erases the earlier source. *)
Lemma filemap_of_nodes_duplicate_different_source_rejects : forall p sf1 sf2,
  filemap_of_nodes (mkFileNode p sf1 :: mkFileNode p sf2 :: nil) = None.
Proof.
  intros p sf1 sf2. apply filemap_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

(** ORDER-INDEPENDENCE (§6): permuting the input nodes yields a SEMANTICALLY EQUAL map ([FilesEqual], not
    record [=]) — construction order never leaks into the source forest. *)
Lemma filemap_of_nodes_permutation : forall nodes1 nodes2 fm1 fm2,
  Permutation nodes1 nodes2 ->
  filemap_of_nodes nodes1 = Some fm1 -> filemap_of_nodes nodes2 = Some fm2 ->
  FilesEqual fm1 fm2.
Proof.
  intros nodes1 nodes2 fm1 fm2 Hperm H1 H2 p.
  destruct (FM.find p fm1) as [sf|] eqn:E1.
  - apply (filemap_of_nodes_find nodes1 fm1 p sf H1) in E1. destruct E1 as [n [Hin [Hp Hs]]].
    symmetry. apply (filemap_of_nodes_find nodes2 fm2 p sf H2).
    exists n. split; [ apply (Permutation_in _ Hperm); exact Hin | split; [ exact Hp | exact Hs ] ].
  - destruct (FM.find p fm2) as [sf|] eqn:E2; [ | reflexivity ].
    exfalso. apply (filemap_of_nodes_find nodes2 fm2 p sf H2) in E2. destruct E2 as [n [Hin [Hp Hs]]].
    assert (Hbad : find_file p fm1 = Some sf).
    { apply (filemap_of_nodes_find nodes1 fm1 p sf H1).
      exists n. split; [ apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin
                       | split; [ exact Hp | exact Hs ] ]. }
    unfold find_file in Hbad. rewrite E1 in Hbad. discriminate.
Qed.


(** ---- the module spec: intrinsic facts about the GENERATED module (not environment config) ---- *)

Record ModuleSpec : Type := mkModuleSpec {
  module_path       : ModulePath;
  module_go_version : GoVersion
}.

(** ---- the program: a module spec + a (possibly empty) standard `FilePath`-keyed source map ([GoFileMap]) ---- *)

Record GoProgram : Type := mkProgram {
  prog_module : ModuleSpec;
  prog_files  : GoFileMap
}.

(** the canonical (FilePath-ordered) DERIVED enumeration of (path, source) bindings — used by the executable
    checkers only; [prog_files] (the map) remains the ONE file authority (typing quantifies over [MapsTo]). *)
Definition prog_bindings (p : GoProgram) : list (FilePath * GoSourceFile) := file_bindings (prog_files p).
Definition prog_keys (p : GoProgram) : list FilePath := file_paths (prog_files p).
Definition prog_find (path : FilePath) (p : GoProgram) : option GoSourceFile := find_file path (prog_files p).

(** ---- builders (the source forest MAY be empty) ---- *)

(** the canonical `package main` source file holding a declaration list (a CONVENIENCE that creates ordinary
    source syntax — the renderer never synthesizes source behind the AST's back). *)
Definition main_source (decls : list GoDecl) : GoSourceFile := mkSourceFile PkgMain [] decls.

(** the canonical `package main` file ROOT at a path (convenience node builder). *)
Definition main_file_node (path : FilePath) (decls : list GoDecl) : GoFileNode :=
  mkFileNode path (main_source decls).

(** A single-file program under a module spec. *)
Definition singleton_program (ms : ModuleSpec) (path : FilePath) (decls : list GoDecl) : GoProgram :=
  mkProgram ms (FM.add path (main_source decls) empty_files).

(** A module-only program: a valid [ModuleSpec] with NO source files. *)
Definition empty_program (ms : ModuleSpec) : GoProgram :=
  mkProgram ms empty_files.

(** The construction API (Master Plan 3.5): from a module spec + a list of specification-shaped file roots,
    [None] ONLY when the collection cannot describe one source tree (chiefly duplicate paths); the EMPTY list
    yields a valid module-only program.  Semantic invalidity remains a compiler result. *)
Definition build_program (ms : ModuleSpec) (nodes : list GoFileNode) : option GoProgram :=
  match filemap_of_nodes nodes with
  | None => None
  | Some fm => Some (mkProgram ms fm)
  end.

(** [build_program] is EXACT over the duplicate-rejecting builder: it succeeds IFF the file paths are unique
    (it fails ONLY on a duplicate path). *)
Theorem build_program_some_iff_unique : forall ms nodes,
  (exists p, build_program ms nodes = Some p) <-> NoDup (List.map file_path nodes).
Proof.
  intros ms nodes. unfold build_program. rewrite <- filemap_of_nodes_success_iff_unique. split.
  - intros [p Hp]. destruct (filemap_of_nodes nodes) as [fm|] eqn:E; [ eexists; reflexivity | discriminate ].
  - intros [fm Hfm]. rewrite Hfm. eexists; reflexivity.
Qed.
