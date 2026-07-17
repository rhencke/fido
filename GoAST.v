(** ============================================================================
    GoAST — the ONE raw program representation.  The permanent root pairs an intrinsic module spec with a
    path-keyed SOURCE FOREST (a [GoFileSet] of specification-shaped file roots; it MAY be empty):

      GoProgram := { prog_module : ModuleSpec ; prog_files : GoFileSet }

    [ModuleSpec] describes the GENERATED Go module itself — its import-path prefix ([ModulePath]) and its
    module-declared language version ([GoVersion]) — NOT ambient execution details (no GOOS/GOARCH/ABI/
    scheduler/point-release/architecture matrix; those stay operationally pinned, off the theorems).  It
    is NOT a TargetConfig.

    A [GoSourceFile] is the specification-shaped RAW source of one file: a package clause ([PkgMain] only
    today), a (currently empty) import section, and top-level declarations — nothing compiled.  The package
    clause is SOURCE-owned (rendered by GoRender); package GROUPING, entry status, and types are COMPILATION /
    TYPING RESULTS — grouping and entry status by GoCompile, types by GoTypes (the one type authority) —
    derived over the whole path-keyed source forest.  There is no raw GoPackage tree and no typed AST: raw
    literals stay UNTYPED syntax.  The file's placement PATH lives on its [GoFileNode] root (one path
    authority), never as a child production inside the source grammar.

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
From Fido Require Import FilePath FMap ModulePath GoVersion Ints Floats Complexes.
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
    C1 — the SPECIFICATION-SHAPED source file root (Master Plan 3.1–3.4).  A source file is no longer a bare
    declaration list: it follows the Go specification's abstract source-file structure — a package clause, a
    (currently empty) import section, and top-level declarations.  The FILE PATH is compilation-unit placement
    metadata carried by the file-ROOT node ([GoFileNode]), NOT a child production inside the source grammar.

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

(** A source file ROOT node: its placement path + its source.  ONE path authority — the path lives here, not
    in a parallel outer-map key. *)
Record GoFileNode : Type := mkFileNode {
  file_path   : FilePath;
  file_source : GoSourceFile
}.

(** A path-keyed source forest: a set of file roots, unique BY CONSTRUCTION on [file_path].  Semantically
    [set[GoFileNode]] with uniqueness by path; physical list order is NOT program semantics. *)
Record GoFileSet : Type := mkFileSet {
  file_members      : list GoFileNode;
  file_paths_unique : NoDup (List.map file_path file_members)
}.

(** ---- the path-keyed file-set API + laws (Master Plan C1.4) ---- *)

Definition file_paths (fs : GoFileSet) : list FilePath := List.map file_path (file_members fs).

(** THE structural invariant: file paths are duplicate-free — same path twice is UNREPRESENTABLE. *)
Definition file_paths_nodup (fs : GoFileSet) : NoDup (file_paths fs) := file_paths_unique fs.

Lemma dup_path_unrepresentable : forall (n1 n2 : GoFileNode),
  file_path n1 = file_path n2 -> ~ NoDup (List.map file_path [n1; n2]).
Proof.
  intros n1 n2 Heq H; simpl in H; inversion H as [ | h t Hni Hnd ]; subst.
  apply Hni. left. symmetry. exact Heq.
Qed.

(** lookup by path — the first (hence, by uniqueness, the ONLY) file root with that path. *)
Definition find_file (p : FilePath) (fs : GoFileSet) : option GoFileNode :=
  List.find (fun n => fp_eqb (file_path n) p) (file_members fs).

(** membership. *)
Definition file_member (n : GoFileNode) (fs : GoFileSet) : Prop := In n (file_members fs).

(** SEMANTIC file-set equality — extensional by path lookup; order/representation-independent (distinct from
    Rocq record [=]). *)
Definition FilesEqual (fs1 fs2 : GoFileSet) : Prop := forall p, find_file p fs1 = find_file p fs2.

(** find is SOUND: a found node is a member carrying exactly the queried path. *)
Lemma find_file_sound : forall p fs n,
  find_file p fs = Some n -> file_member n fs /\ file_path n = p.
Proof.
  intros p fs n H. unfold find_file in H. apply List.find_some in H as [Hin Hpred].
  apply fp_eqb_eq in Hpred. split; [ exact Hin | exact Hpred ].
Qed.

(** find is COMPLETE: a member with the queried path IS found (and, by uniqueness, it is that exact node). *)
Lemma find_file_complete : forall p fs n,
  file_member n fs -> file_path n = p -> find_file p fs = Some n.
Proof.
  intros p fs n. unfold file_member, find_file. destruct fs as [members Hnd]. simpl.
  induction members as [ | h t IH ]; simpl; [ intros [] | ].
  simpl in Hnd. inversion Hnd as [ | hh tt Hni Hnd' ]; subst.
  intros [Hhn | Hin] Hpath.
  - subst h. rewrite (proj2 (fp_eqb_eq (file_path n) p) Hpath). reflexivity.
  - destruct (fp_eqb (file_path h) p) eqn:E.
    + exfalso. apply fp_eqb_eq in E. apply Hni. rewrite E, <- Hpath.
      apply List.in_map. exact Hin.
    + apply IH; [ exact Hnd' | exact Hin | exact Hpath ].
Qed.

(** find is FUNCTIONAL and DETERMINISTIC: a path locates at most one file root. *)
Lemma find_file_fun : forall p fs n1 n2,
  find_file p fs = Some n1 -> find_file p fs = Some n2 -> n1 = n2.
Proof. intros p fs n1 n2 H1 H2. rewrite H1 in H2. injection H2 as <-. reflexivity. Qed.

(** [FilesEqual] is an equivalence — the semantic identity of file sets. *)
Lemma FilesEqual_refl : forall fs, FilesEqual fs fs.
Proof. intros fs p. reflexivity. Qed.
Lemma FilesEqual_sym : forall fs1 fs2, FilesEqual fs1 fs2 -> FilesEqual fs2 fs1.
Proof. intros fs1 fs2 H p. symmetry. apply H. Qed.
Lemma FilesEqual_trans : forall fs1 fs2 fs3, FilesEqual fs1 fs2 -> FilesEqual fs2 fs3 -> FilesEqual fs1 fs3.
Proof. intros fs1 fs2 fs3 H12 H23 p. rewrite H12. apply H23. Qed.

(** ---- the empty file set, a singleton, and a duplicate-rejecting list builder ---- *)

Lemma nodup_nil_path : NoDup (List.map file_path (@nil GoFileNode)).
Proof. constructor. Qed.
Definition fs_empty : GoFileSet := mkFileSet [] nodup_nil_path.

Lemma nodup_singleton_path : forall n : GoFileNode, NoDup (List.map file_path [n]).
Proof. intro n; simpl; constructor; [ intro H; inversion H | constructor ]. Qed.
Definition fs_singleton (n : GoFileNode) : GoFileSet := mkFileSet [n] (nodup_singleton_path n).

Fixpoint no_dup_pathsb (l : list GoFileNode) : bool :=
  match l with
  | [] => true
  | n :: l' => negb (existsb (fun m => fp_eqb (file_path n) (file_path m)) l') && no_dup_pathsb l'
  end.

Lemma existsb_path_In : forall (p : FilePath) (l : list GoFileNode),
  existsb (fun m => fp_eqb p (file_path m)) l = true <-> In p (List.map file_path l).
Proof.
  intros p l; induction l as [ | m l' IH ]; simpl.
  - split; [ discriminate | intros [] ].
  - rewrite Bool.orb_true_iff, IH. split.
    + intros [He | Hin]; [ left; symmetry; apply fp_eqb_eq; exact He | right; exact Hin ].
    + intros [He | Hin]; [ left; apply fp_eqb_eq; symmetry; exact He | right; exact Hin ].
Qed.

Lemma no_dup_pathsb_correct : forall l, no_dup_pathsb l = true -> NoDup (List.map file_path l).
Proof.
  induction l as [ | n l' IH ]; simpl; intro H.
  - constructor.
  - apply Bool.andb_true_iff in H; destruct H as [Hne Hrest].
    constructor.
    + rewrite <- existsb_path_In. rewrite Bool.negb_true_iff in Hne. rewrite Hne. discriminate.
    + apply IH; exact Hrest.
Qed.

(** From a list of file roots: [None] ONLY on a duplicate path; the EMPTY list yields the empty file set. *)
Definition fileset_of_list (l : list GoFileNode) : option GoFileSet :=
  (match no_dup_pathsb l as b return no_dup_pathsb l = b -> option GoFileSet with
   | true  => fun H => Some (mkFileSet l (no_dup_pathsb_correct l H))
   | false => fun _ => None
   end) eq_refl.

Lemma fileset_of_list_members : forall l fs, fileset_of_list l = Some fs -> file_members fs = l.
Proof.
  intros l fs. unfold fileset_of_list.
  generalize (@eq_refl bool (no_dup_pathsb l)).
  destruct (no_dup_pathsb l) at 2 3; intro H; [ | discriminate ].
  intro Heq; injection Heq as <-; reflexivity.
Qed.

(** ---- the module spec: intrinsic facts about the GENERATED module (not environment config) ---- *)

Record ModuleSpec : Type := mkModuleSpec {
  module_path       : ModulePath;
  module_go_version : GoVersion
}.

(** ---- the program: a module spec + a (possibly empty) path-keyed SOURCE FOREST ([GoFileSet]) ---- *)

Record GoProgram : Type := mkProgram {
  prog_module : ModuleSpec;
  prog_files  : GoFileSet
}.

(** the (path, declarations) enumeration — a DERIVED view of the source forest for the semantic layers
    (typing / main-counting) that read only declarations; [prog_files] remains the ONE file authority. *)
Definition prog_entries (p : GoProgram) : list (FilePath * list GoDecl) :=
  List.map (fun n => (file_path n, source_decls (file_source n))) (file_members (prog_files p)).
Definition prog_keys (p : GoProgram) : list FilePath := file_paths (prog_files p).
Definition prog_find (path : FilePath) (p : GoProgram) : option GoSourceFile :=
  option_map file_source (find_file path (prog_files p)).

(** render each source file into a value, keyed by its path — a TRUE finite map (paths unique by
    construction).  This is how the emitter enumerates the rendered forest without a second authority. *)
Definition fileset_entries {A} (r : GoSourceFile -> A) (fs : GoFileSet) : list (FilePath * A) :=
  List.map (fun n => (file_path n, r (file_source n))) (file_members fs).
Lemma fileset_entries_keys {A} (r : GoSourceFile -> A) (fs : GoFileSet) :
  List.map fst (fileset_entries r fs) = file_paths fs.
Proof. unfold fileset_entries, file_paths. rewrite List.map_map. reflexivity. Qed.
Definition fileset_fmap {A} (r : GoSourceFile -> A) (fs : GoFileSet) : fmap FilePath A :=
  mkFMap (fileset_entries r fs)
         (eq_ind_r (fun ks => NoDup ks) (file_paths_unique fs) (fileset_entries_keys r fs)).

(** ---- builders (paths unique, intrinsic; the source forest MAY be empty) ---- *)

(** the canonical `package main` source file holding a declaration list. *)
Definition main_source (decls : list GoDecl) : GoSourceFile := mkSourceFile PkgMain [] decls.

(** A single-file program under a module spec. *)
Definition singleton_program (ms : ModuleSpec) (path : FilePath) (decls : list GoDecl) : GoProgram :=
  mkProgram ms (fs_singleton (mkFileNode path (main_source decls))).

(** A module-only program: a valid [ModuleSpec] with NO source files. *)
Definition empty_program (ms : ModuleSpec) : GoProgram :=
  mkProgram ms fs_empty.

(** From a module spec + a list of (path, declarations): [None] ONLY on duplicate paths; the EMPTY list
    yields a valid module-only program (path-uniqueness is intrinsic). *)
Definition build_program (ms : ModuleSpec) (l : list (FilePath * list GoDecl)) : option GoProgram :=
  match fileset_of_list (List.map (fun pe => mkFileNode (fst pe) (main_source (snd pe))) l) with
  | None => None
  | Some fs => Some (mkProgram ms fs)
  end.
