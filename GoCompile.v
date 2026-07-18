(** ============================================================================
    GoCompile — EXACT whole-PROGRAM static/compiler admissibility as EVIDENCE over the ONE raw program
    (the [GoProgram]: a [ModuleSpec] + a possibly-EMPTY standard [FilePath] map of files [GoFileMap]), plus the
    derived admissibility evidence ([ProgValid]) over that same program.  The empty program is accepted (no
    packages, one go.mod).

    Whole-program package policy (a deliberate exact GENERATOR-language subset).  The package CLAUSE / NAME is
    SOURCE syntax (each file's [source_package], [PkgMain] -> `main`, rendered by GoRender) — NOT a compiler-
    derived name; imports are INTRINSICALLY absent today ([source_imports] is `nil` by construction).  Package
    GROUPING and main/entry validity are COMPILATION RESULTS over the whole program:
      - files are grouped by parent directory ([fp_parent]) — via a one-pass standard [PackageMap]; each
        directory is one package;
      - every package must contain EXACTLY ONE admissible `main` declaration across all its files
        (zero rejects the whole program; more than one rejects the whole program);
      - the whole program is TYPED through [GoTypes] ([ProgramTyped] — every `println` argument resolves to a
        [GoType]: a constant fits its resolved integer/float/complex type and every explicit integer/float/
        complex conversion is valid — the one [convert_const] authority);
      - one invalid package rejects the WHOLE program (all-or-nothing; no per-file partial acceptance);
      - multiple valid main packages in different directories are accepted, matching `go build ./...`;
      - an empty file is accepted when its package's single `main` is elsewhere.

    HONESTY — two distinct claims:
    A. KERNEL-internal exactness (PROVED here): [go_compile] succeeds exactly for the declarative
       [GoCompile] judgment ([prog_ok_iff]; sound + complete).
    B. EXTERNAL adequacy (the GOAL, attacked by differential `go build ./...` experiments, NOT a kernel
       theorem): the declarative judgment matches `go build ./...` for every representable rendered
       program.  We do NOT invoke cmd/go from Rocq and claim no kernel theorem about it.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool String Arith Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Ints Floats Complexes FilePath Collections GoAST GoIndex GoTypes.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
Open Scope Z_scope.

(** ---- static admissibility is TYPING (GoTypes, the one type authority) ----

    Per-file/decl/statement/expression admissibility is [GoTypes.ProgramTyped]/[program_typedb] over the
    SAME raw AST: every [println] argument must RESOLVE under [UsePrintlnArg] to a [GoType] (a typing failure
    is a constant fitting no integer type, a bare float overflowing its default [float64], an invalid
    [EIntConvert]/[EFloatConvert]/[EComplexConvert] — a float or complex-component overflow, a fractional or
    out-of-range float->integer, a nonzero-imaginary complex->scalar, a wrong-type or
    nested-invalid conversion; bools and strings always resolve).  There is no separate GoCompile static-
    admissibility family; the deleted [ExprOk]/[StmtOk]/[DeclOk]/[FileOk] are subsumed by the type judgment. *)

(** ---- main-declaration counting (entry-point status is a compilation result) ---- *)

Definition decl_is_main (d : GoDecl) : bool := match d with DMain _ => true end.
Definition file_main_count (decls : list GoDecl) : nat := List.length (List.filter decl_is_main decls).

Module PM := Collections.PackageMapBase.
Module PMF := Collections.PackageMapFacts.
Module PMP := Collections.PackageMapProps.

(** a package (directory) SUMMARY carries only the LIVE fact the current fragment needs — the package's total
    `main` declaration count.  (No speculative method/import/type fields; a new fact lands with its proofs.) *)
Record PackageSummary : Type := mkPkgSummary { ps_main_count : nat }.
Definition ps_count (o : option PackageSummary) : nat := match o with Some s => ps_main_count s | None => 0 end.

(** accumulate one file's `main` count into its parent-directory package summary. *)
Definition pm_add_main (dir : string) (n : nat) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  PM.add dir (mkPkgSummary (n + ps_count (PM.find dir acc))) acc.
Definition pkg_step (path : FilePath) (sf : GoSourceFile) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  pm_add_main (fp_parent path) (file_main_count (source_decls sf)) acc.

(** ONE pass over the file MAP (C1A §8): a single [FM.fold] over the source forest, each file contributing its
    `main` count EXACTLY ONCE to its parent-directory package summary via one logarithmic [PackageMap] update —
    NOT a repeated O(files²) file scan (the deleted [main_count_in_dir] scanned all entries per file). *)
Definition package_summaries (fm : GoFileMap) : PM.t PackageSummary :=
  GoAST.FM.fold pkg_step fm (PM.empty PackageSummary).

(** ---- the declarative validity of the whole program ---- *)

(** Every package (directory) has exactly one `main` declaration — quantified over the PACKAGE-MAP bindings. *)
Definition AllPackagesOneMain (p : GoProgram) : Prop :=
  forall dir s, PM.MapsTo dir s (package_summaries (prog_files p)) -> ps_main_count s = 1%nat.

(** A program is valid iff it is TYPED (every argument resolves through [GoTypes]) AND every package has
    exactly one `main`.  [ProgramTyped] is the one static-typing foundation; there is no parallel
    admissibility family. *)
Definition ProgValid (p : GoProgram) : Prop := ProgramTyped p /\ AllPackagesOneMain p.

Definition prog_ok (p : GoProgram) : bool :=
  program_typedb p
  && forallb (fun b => Nat.eqb (ps_main_count (snd b)) 1) (PM.elements (package_summaries (prog_files p))).

Lemma prog_ok_iff : forall p, prog_ok p = true <-> ProgValid p.
Proof.
  intro p. unfold prog_ok, ProgValid, AllPackagesOneMain.
  rewrite Bool.andb_true_iff, program_typedb_iff.
  rewrite (forallb_Forall (fun b => Nat.eqb (ps_main_count (snd b)) 1%nat) (fun b => ps_main_count (snd b) = 1%nat)
             (PM.elements (package_summaries (prog_files p))) (fun b => Nat.eqb_eq (ps_main_count (snd b)) 1%nat)).
  split.
  - intros [Ht Hf]. split; [ exact Ht | ]. intros dir s Hmt.
    apply PMF.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros [Ht Hall]. split; [ exact Ht | ]. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PMF.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

(** ---- §8 PACKAGE-SUMMARY EXACTNESS: the single [FM.fold] is characterized EXACTLY, so package grouping is
    provably a one-pass, order-independent, map-extensional aggregation. ---- *)

(* the SPEC: the total `main` count files whose parent directory is [dir] contribute to that package. *)
Fixpoint list_dir_count (dir : string) (l : list (FilePath * GoSourceFile)) : nat :=
  match l with
  | [] => 0
  | b :: rest =>
      (if String.eqb (fp_parent (fst b)) dir then file_main_count (source_decls (snd b)) else 0)
      + list_dir_count dir rest
  end.
Definition list_dir_mem (dir : string) (l : list (FilePath * GoSourceFile)) : bool :=
  existsb (fun b => String.eqb (fp_parent (fst b)) dir) l.

Lemma list_dir_count_0 : forall dir l, list_dir_mem dir l = false -> list_dir_count dir l = 0%nat.
Proof.
  intros dir l; induction l as [|b rest IH]; simpl; [ reflexivity | ].
  unfold list_dir_mem in *; simpl; intro H. apply Bool.orb_false_iff in H as [Hb Hr].
  rewrite Hb; simpl; apply IH; exact Hr.
Qed.

(* list-level order-independence: both the presence flag and the count are permutation-invariant sums. *)
Lemma list_dir_mem_perm : forall dir l1 l2, Permutation l1 l2 -> list_dir_mem dir l1 = list_dir_mem dir l2.
Proof.
  intros dir l1 l2 H; unfold list_dir_mem; induction H; simpl; try reflexivity.
  - rewrite IHPermutation; reflexivity.
  - destruct (String.eqb (fp_parent (fst y)) dir), (String.eqb (fp_parent (fst x)) dir); reflexivity.
  - rewrite IHPermutation1; exact IHPermutation2.
Qed.
Lemma list_dir_count_perm : forall dir l1 l2, Permutation l1 l2 -> list_dir_count dir l1 = list_dir_count dir l2.
Proof.
  intros dir l1 l2 H; induction H; simpl; lia.
Qed.

(* the left fold matching [FM.fold] over the element list. *)
Definition pkg_foldl (l : list (FilePath * GoSourceFile)) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  fold_left (fun a p => pkg_step (fst p) (snd p) a) l acc.
Lemma pkg_foldl_cons : forall k e rest acc,
  pkg_foldl ((k, e) :: rest) acc = pkg_foldl rest (pkg_step k e acc).
Proof. reflexivity. Qed.
Lemma package_summaries_foldl : forall fm,
  package_summaries fm = pkg_foldl (GoAST.file_bindings fm) (PM.empty PackageSummary).
Proof. intro fm. unfold package_summaries, pkg_foldl. rewrite GoAST.FM.fold_1. reflexivity. Qed.

(* the fold CHARACTERIZATION: [find dir] is present iff a file belongs to [dir], and equals the exact sum. *)
Lemma pkg_foldl_find : forall l acc dir,
  PM.find dir (pkg_foldl l acc)
  = (if list_dir_mem dir l
     then Some (mkPkgSummary (list_dir_count dir l + ps_count (PM.find dir acc)))
     else PM.find dir acc).
Proof.
  induction l as [|[k e] rest IH]; intros acc dir; [ reflexivity | ].
  rewrite pkg_foldl_cons, (IH (pkg_step k e acc) dir).
  unfold list_dir_mem; simpl existsb; simpl list_dir_count; cbn [fst snd].
  destruct (String.eqb (fp_parent k) dir) eqn:Edir; cbn [orb].
  - apply String.eqb_eq in Edir.
    unfold pkg_step, pm_add_main. rewrite !PMF.add_eq_o by exact Edir.
    cbn [ps_count ps_main_count]. rewrite !Edir.
    destruct (existsb (fun b => String.eqb (fp_parent (fst b)) dir) rest) eqn:Erest;
      [ | rewrite (list_dir_count_0 dir rest Erest) ]; f_equal; f_equal; lia.
  - apply String.eqb_neq in Edir.
    unfold pkg_step, pm_add_main. rewrite !PMF.add_neq_o by exact Edir. reflexivity.
Qed.

Definition pkg_main_count (dir : string) (fm : GoFileMap) : nat := list_dir_count dir (GoAST.file_bindings fm).

Lemma package_summaries_find : forall fm dir,
  PM.find dir (package_summaries fm)
  = (if list_dir_mem dir (GoAST.file_bindings fm)
     then Some (mkPkgSummary (pkg_main_count dir fm)) else None).
Proof.
  intros fm dir. rewrite package_summaries_foldl, pkg_foldl_find. unfold pkg_main_count.
  rewrite PMF.empty_o. cbn [ps_count].
  destruct (list_dir_mem dir (GoAST.file_bindings fm)); [ f_equal; f_equal; lia | reflexivity ].
Qed.

(* THEOREM (§8.1): every represented file contributes to its OWN parent-directory package (which is present). *)
Theorem file_in_package : forall fm path sf,
  GoAST.maps_to_file path sf fm -> PM.In (fp_parent path) (package_summaries fm).
Proof.
  intros fm path sf Hmt.
  assert (Hin : In (path, sf) (GoAST.file_bindings fm)).
  { unfold GoAST.file_bindings. apply GoAST.FMF.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
    destruct Hmt as [[k' e'] [[Hk He] Hin']]. cbn in Hk, He. subst. exact Hin'. }
  exists (mkPkgSummary (pkg_main_count (fp_parent path) fm)).
  apply PMF.find_mapsto_iff. rewrite package_summaries_find.
  assert (Hmem : list_dir_mem (fp_parent path) (GoAST.file_bindings fm) = true).
  { unfold list_dir_mem. apply existsb_exists. exists (path, sf).
    split; [ exact Hin | cbn [fst]; apply String.eqb_refl ]. }
  rewrite Hmem. reflexivity.
Qed.

(* THEOREM (§8.2): no package summary exists without a file — a present [dir] is witnessed by a real file. *)
Theorem package_no_empty : forall fm dir,
  PM.In dir (package_summaries fm) ->
  exists b, In b (GoAST.file_bindings fm) /\ fp_parent (fst b) = dir.
Proof.
  intros fm dir [s Hmt]. apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (GoAST.file_bindings fm)) eqn:Emem; [ | discriminate ].
  unfold list_dir_mem in Emem. apply existsb_exists in Emem. destruct Emem as [b [Hin Heq]].
  apply String.eqb_eq in Heq. exists b. split; [ exact Hin | exact Heq ].
Qed.

(* THEOREM (§8.3): a package summary's main count IS the sum of [file_main_count] over its files. *)
Theorem package_summary_main_count : forall fm dir s,
  PM.MapsTo dir s (package_summaries fm) -> ps_main_count s = pkg_main_count dir fm.
Proof.
  intros fm dir s Hmt. apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (GoAST.file_bindings fm)); [ | discriminate ].
  injection Hmt as <-. reflexivity.
Qed.

(* THEOREM (§8.4): the empty file map yields the empty package map. *)
Theorem package_summaries_empty : forall dir,
  PM.find dir (package_summaries empty_files) = None.
Proof.
  intro dir. rewrite package_summaries_find.
  replace (GoAST.file_bindings empty_files) with (@nil (FilePath * GoSourceFile)); [ reflexivity | ].
  unfold GoAST.file_bindings, empty_files. symmetry. apply Collections.FileMapProps.elements_empty.
Qed.

(* THEOREM (§8.5): map-equal file collections yield map-equal package summaries — order/structure of the
   backing tree never leaks.  Proved by the standard [fold_Equal] (the aggregation is a proper, key-transpose
   fold), so no element-list reasoning is needed. *)
Instance PM_Equal_Equiv : Equivalence (@PM.Equal PackageSummary).
Proof.
  constructor.
  - intros m k; reflexivity.
  - intros m1 m2 H k; symmetry; apply H.
  - intros m1 m2 m3 H1 H2 k; transitivity (PM.find k m2); [ apply H1 | apply H2 ].
Qed.
Lemma pkg_step_Proper : Proper (GoAST.FM.E.eq ==> eq ==> PM.Equal ==> PM.Equal) pkg_step.
Proof.
  intros k1 k2 Hk e1 e2 He a1 a2 Ha dk.
  assert (Hkk : k1 = k2) by exact Hk. subst k2. subst e2.
  unfold pkg_step, pm_add_main.
  destruct (String.eqb (fp_parent k1) dk) eqn:E.
  - apply String.eqb_eq in E. rewrite !PMF.add_eq_o by exact E. rewrite (Ha (fp_parent k1)); reflexivity.
  - apply String.eqb_neq in E. rewrite !PMF.add_neq_o by exact E. apply Ha.
Qed.
Lemma pkg_foldl_permutation : forall l1 l2 acc,
  Permutation l1 l2 -> PM.Equal (pkg_foldl l1 acc) (pkg_foldl l2 acc).
Proof.
  intros l1 l2 acc Hperm dir. rewrite !pkg_foldl_find.
  rewrite (list_dir_mem_perm dir l1 l2 Hperm), (list_dir_count_perm dir l1 l2 Hperm). reflexivity.
Qed.
Lemma pkg_step_transpose : Collections.FileMapProps.transpose_neqkey PM.Equal pkg_step.
Proof.
  intros k1 k2 e1 e2 a _.
  change (pkg_step k1 e1 (pkg_step k2 e2 a)) with (pkg_foldl ((k2, e2) :: (k1, e1) :: nil) a).
  change (pkg_step k2 e2 (pkg_step k1 e1 a)) with (pkg_foldl ((k1, e1) :: (k2, e2) :: nil) a).
  apply pkg_foldl_permutation. apply perm_swap.
Qed.
Theorem package_summaries_Equal : forall fm1 fm2,
  GoAST.FilesEqual fm1 fm2 -> PM.Equal (package_summaries fm1) (package_summaries fm2).
Proof.
  intros fm1 fm2 Heq. unfold package_summaries.
  apply (Collections.FileMapProps.fold_Equal PM_Equal_Equiv pkg_step_Proper pkg_step_transpose). exact Heq.
Qed.

(* THEOREM (§8.6): reordered construction yields map-equal package summaries — a permuted node list builds a
   [FilesEqual] map (§6), so its package aggregation is unchanged. *)
Theorem package_summaries_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  PM.Equal (package_summaries (prog_files p1)) (package_summaries (prog_files p2)).
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply package_summaries_Equal.
  unfold build_program in *.
  destruct (filemap_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(** ---- whole-program admissibility over the SAME program ---- *)

(* ============================================================================================================
   §7 (C3) — PackageRef: a VALIDATED absence anchor for package-level diagnostics.  A package spans files and is
   not one AST node, so a missing-main diagnostic anchors at a proof-backed package handle, never a fake source
   node.  Identity is the package KEY (parent-directory string); the proof field is a BOOLEAN membership
   equation (UIP over bool), so key equality determines the ref AND a PackageRef cannot name a package with no
   represented file.
   ============================================================================================================ *)

Definition package_present_b (p : GoProgram) (key : string) : bool :=
  list_dir_mem key (GoAST.file_bindings (prog_files p)).

Record PackageRef (p : GoProgram) : Type := mkPackageRef {
  package_ref_key : string ;
  package_ref_ok  : package_present_b p package_ref_key = true
}.
Arguments package_ref_key {p} _.
Arguments package_ref_ok {p} _.

(** represented-package witness: a PackageRef's key names a real file in [p] (the directive's §7 exists form). *)
Lemma package_ref_present : forall p (r : PackageRef p),
  exists path sf, GoAST.maps_to_file path sf (prog_files p) /\ fp_parent path = package_ref_key r.
Proof.
  intros p [k ok]; cbn. unfold package_present_b, list_dir_mem in ok.
  apply existsb_exists in ok. destruct ok as [b [Hin Heqb]]. apply String.eqb_eq in Heqb.
  exists (fst b), (snd b). split; [ | exact Heqb ].
  unfold GoAST.maps_to_file. apply GoAST.FMF.find_mapsto_iff.
  exact (GoAST.file_bindings_find (prog_files p) b Hin).
Qed.

(** identity IS key identity (the boolean proof field is irrelevant by UIP over bool — no axiom). *)
Lemma package_ref_key_inj : forall p (r1 r2 : PackageRef p),
  package_ref_key r1 = package_ref_key r2 -> r1 = r2.
Proof.
  intros p [k1 ok1] [k2 ok2] Heq; cbn in Heq; subst k2.
  f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Definition package_ref_eq_dec : forall p (r1 r2 : PackageRef p), {r1 = r2} + {r1 <> r2}.
Proof.
  intros p r1 r2. destruct (string_dec (package_ref_key r1) (package_ref_key r2)) as [He|Hne].
  - left. apply package_ref_key_inj; exact He.
  - right. intro H; apply Hne; rewrite H; reflexivity.
Defined.

(** construction from a real file binding: its package (parent directory) is present (the binding witnesses it). *)
Definition package_ref_of_binding (p : GoProgram) (b : FilePath * GoSourceFile)
  (Hin : In b (GoAST.file_bindings (prog_files p))) : PackageRef p.
Proof.
  refine (mkPackageRef p (fp_parent (fst b)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists b. split; [ exact Hin | apply String.eqb_refl ].
Defined.

Lemma package_ref_of_binding_key : forall p b Hin,
  package_ref_key (package_ref_of_binding p b Hin) = fp_parent (fst b).
Proof. reflexivity. Qed.

(** construction from a validated file reference: the ref's own path witnesses its package. *)
Definition package_ref_of_fileref {p} (fr : GoIndex.Snap.FileRef p) : PackageRef p.
Proof.
  refine (mkPackageRef p (fp_parent (GoIndex.Snap.file_ref_path fr)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists (GoIndex.Snap.file_ref_path fr, GoIndex.Snap.file_ref_source fr). split.
  - apply GoAST.find_file_bindings.
    apply (GoIndex.Snap.file_of_path_source_exact p (GoIndex.Snap.file_ref_path fr) fr).
    apply GoIndex.Snap.file_of_path_complete.
  - apply String.eqb_refl.
Defined.

Lemma package_ref_of_fileref_key : forall p (fr : GoIndex.Snap.FileRef p),
  package_ref_key (package_ref_of_fileref fr) = fp_parent (GoIndex.Snap.file_ref_path fr).
Proof. reflexivity. Qed.

(* ============================================================================================================
   §8 (C3) — the structured diagnostic core.  Every anchor is an EXACT-SNAPSHOT handle (a NodeRef / FileRef /
   PackageRef of [p], or the whole program); the four current diagnostic reasons carry TYPED references
   (ExprRef / DeclRef) and structured values, so an invalid anchor/category combination is unrepresentable.
   The core carries codes + valid anchors + structured values — NO authoritative English prose (a pure report
   projection produces readable text later, §24).
   ============================================================================================================ *)

Inductive DiagnosticAnchor (p : GoProgram) : Type :=
| AtNode    : GoIndex.Snap.NodeRef p -> DiagnosticAnchor p
| AtFile    : GoIndex.Snap.FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.
Arguments AtNode {p} _.  Arguments AtFile {p} _.  Arguments AtPackage {p} _.  Arguments AtProgram {p}.

(* the four current C3 diagnostic reasons.  Nested invalid conversions: [primary] is the INNERMOST failing
   conversion, [outer_context] the enclosing conversions (nearest first).  Duplicate main: [later_primary]
   the later declaration, [earlier_related] the first (canonical-order) main. *)
Inductive DiagnosticReason (p : GoProgram) : Type :=
| DRInvalidConversion
    (primary : GoIndex.ExprRef p) (outer_context : list (GoIndex.ExprRef p))
    (target : GoType) (operand_status : ConstInfo)
| DRDefaultNotRepresentable
    (primary : GoIndex.ExprRef p) (exact_constant : GoConst) (default_target : GoType)
| DRDuplicateMain
    (later_primary : GoIndex.DeclRef p) (earlier_related : GoIndex.DeclRef p)
| DRMissingMain
    (package_primary : PackageRef p).
Arguments DRInvalidConversion {p} _ _ _ _.  Arguments DRDefaultNotRepresentable {p} _ _ _.
Arguments DRDuplicateMain {p} _ _.  Arguments DRMissingMain {p} _.

Inductive DiagnosticCode : Type :=
| DCInvalidConversion | DCDefaultNotRepresentable | DCDuplicateMain | DCMissingMain.

Definition diagnostic_code_eq_dec (a b : DiagnosticCode) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* a stable finite ordering of the codes (for canonical per-anchor bucket order, §16). *)
Definition diagnostic_code_index (c : DiagnosticCode) : nat :=
  match c with
  | DCInvalidConversion => 0 | DCDefaultNotRepresentable => 1 | DCDuplicateMain => 2 | DCMissingMain => 3
  end.

Definition diagnostic_code {p} (d : DiagnosticReason p) : DiagnosticCode :=
  match d with
  | DRInvalidConversion _ _ _ _   => DCInvalidConversion
  | DRDefaultNotRepresentable _ _ _ => DCDefaultNotRepresentable
  | DRDuplicateMain _ _           => DCDuplicateMain
  | DRMissingMain _               => DCMissingMain
  end.

Definition diagnostic_primary {p} (d : DiagnosticReason p) : DiagnosticAnchor p :=
  match d with
  | DRInvalidConversion pr _ _ _      => AtNode (GoIndex.erase_ref pr)
  | DRDefaultNotRepresentable pr _ _  => AtNode (GoIndex.erase_ref pr)
  | DRDuplicateMain later _           => AtNode (GoIndex.erase_ref later)
  | DRMissingMain pk                  => AtPackage pk
  end.

Definition diagnostic_related {p} (d : DiagnosticReason p) : list (DiagnosticAnchor p) :=
  match d with
  | DRInvalidConversion _ outer _ _   => map (fun r => AtNode (GoIndex.erase_ref r)) outer
  | DRDefaultNotRepresentable _ _ _   => []
  | DRDuplicateMain _ earlier         => [AtNode (GoIndex.erase_ref earlier)]
  | DRMissingMain _                   => []
  end.

(** the primary anchor is always an exact-snapshot handle whose CODE matches the reason. *)
Lemma diagnostic_code_primary_consistent : forall p (d : DiagnosticReason p),
  match diagnostic_code d, diagnostic_primary d with
  | DCMissingMain, AtPackage _ => True
  | DCInvalidConversion, AtNode _ | DCDefaultNotRepresentable, AtNode _ | DCDuplicateMain, AtNode _ => True
  | _, _ => False
  end.
Proof. intros p [pr o t s|pr c dt|l e|pk]; cbn; exact I. Qed.

(* ============================================================================================================
   §10 (C3) — occurrence-keyed expression facts.  ONE fact value per expression occurrence: its exact constant
   status ([const_info]) plus, ONLY for a use-context (println-argument) occurrence, its resolved constant
   ([resolve_expr_const UsePrintlnArg]).  Type and resolved exact value are PROJECTIONS from the one
   [ResolvedConst] — no parallel type map that could disagree.  Facts store semantic values only (never a
   GoExpr / SourceOccurrence / rewritten syntax).
   ============================================================================================================ *)

Record ExprFact : Type := mkExprFact {
  ef_const_status : ConstInfo ;
  ef_use_resolved : option ResolvedConst
}.

Definition resolved_type_at (f : ExprFact) : option GoType :=
  option_map resolved_const_type (ef_use_resolved f).
Definition resolved_constant_at (f : ExprFact) : option GoConst :=
  option_map resolved_const_exact (ef_use_resolved f).

(** the use-context resolution an occurrence carries: [Some rc] EXACTLY for a println-argument expression that
    resolves, else [None] (a conversion operand / internal expression, or a non-resolving argument). *)
Definition occ_use_resolved (o : GoIndex.SourceOccurrence) : option ResolvedConst :=
  match GoIndex.occurrence_role o with
  | GoIndex.RPrintlnArg _ =>
      match GoIndex.view_expr o with Some e => resolve_expr_const UsePrintlnArg e | None => None end
  | _ => None
  end.

(** the fact of a single occurrence: [Some] exactly for an expression occurrence whose [const_info] succeeds. *)
Definition occ_expr_fact (o : GoIndex.SourceOccurrence) : option ExprFact :=
  match GoIndex.view_expr o with
  | Some e => match const_info e with
              | Some ci => Some (mkExprFact ci (occ_use_resolved o))
              | None => None
              end
  | None => None
  end.

(** an occurrence has a fact IFF it is an expression whose const_info succeeds; the fact's status is exactly
    that [const_info], and its resolved field is exactly the occurrence's use-context resolution. *)
Lemma occ_expr_fact_status : forall o e ci,
  GoIndex.view_expr o = Some e -> const_info e = Some ci ->
  occ_expr_fact o = Some (mkExprFact ci (occ_use_resolved o)).
Proof. intros o e ci Hv Hc. unfold occ_expr_fact. rewrite Hv, Hc. reflexivity. Qed.

Lemma occ_expr_fact_none_nonexpr : forall o,
  GoIndex.view_expr o = None -> occ_expr_fact o = None.
Proof. intros o Hv. unfold occ_expr_fact. rewrite Hv. reflexivity. Qed.

(** the per-file expression-fact map: fold the §19 visit stream, keying each occurrence's fact by its NodeKey.
    Non-expression / const_info-failed occurrences contribute nothing.  Because [visit_file] keys are DISTINCT
    (NoDup), the fold never overwrites, and the stored fact at each ref's key is EXACTLY that occurrence's fact. *)
Definition add_occ_fact {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) : GoIndex.NodeKeyMapBase.t ExprFact :=
  match occ_expr_fact (snd ro) with
  | Some f => GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (fst ro)) f m
  | None => m
  end.

Definition file_expr_facts {p} (fr : GoIndex.Snap.FileRef p) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) (GoIndex.Snap.visit_file fr).

Lemma NoDup_map_inj {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj H. induction H as [|x l Hx Hnd IH]; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]]. apply Hinj in Hfy. subst y. contradiction.
  - exact IH.
Qed.

(** the [visit_file] refs have DISTINCT NodeKeys (same file, distinct local ids). *)
Lemma visit_file_key_nodup {p} (fr : GoIndex.Snap.FileRef p) :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (GoIndex.Snap.visit_file fr)).
Proof.
  assert (Hmap : map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (GoIndex.Snap.visit_file fr)
    = map (fun ro => GoIndex.mkKey (GoIndex.Snap.file_ref_path fr) (GoIndex.Snap.node_ref_local (fst ro)))
          (GoIndex.Snap.visit_file fr)).
  { apply map_ext_in. intros [r occ] Hin. cbn [fst]. rewrite GoIndex.Snap.node_ref_key_eq.
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity. }
  rewrite Hmap, <- (map_map (fun ro => GoIndex.Snap.node_ref_local (fst ro))
                            (GoIndex.mkKey (GoIndex.Snap.file_ref_path fr))).
  apply NoDup_map_inj; [ intros x y H; injection H as H; exact H | apply GoIndex.Snap.visit_file_nodup ].
Qed.

Lemma facts_not_in_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (k : GoIndex.NodeKey) :
  ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  GoIndex.NodeKeyMapBase.find k (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = None.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hni; simpl.
  - apply GoIndex.NodeKeyMapFacts.empty_o.
  - simpl in Hni.
    assert (Hne : GoIndex.Snap.node_ref_key r0 <> k) by (intro H; apply Hni; left; exact H).
    assert (Hrest : ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest))
      by (intro H; apply Hni; right; exact H).
    unfold add_occ_fact; cbn [snd fst]. destruct (occ_expr_fact occ0) as [f|].
    + rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact (IH Hrest).
    + exact (IH Hrest).
Qed.

Lemma fold_facts_find {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) r occ :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  In (r, occ) l ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r)
    (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = occ_expr_fact occ.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hnd Hin; [ destruct Hin |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  simpl. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. unfold add_occ_fact; cbn [snd fst].
    destruct (occ_expr_fact occ0) as [f|] eqn:Ef.
    + rewrite GoIndex.nodekeymap_add_eq. reflexivity.
    + apply facts_not_in_domain. exact Hni.
  - assert (Hin' : In (GoIndex.Snap.node_ref_key r)
             (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest)).
    { apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hin]. }
    assert (Hkr : GoIndex.Snap.node_ref_key r <> GoIndex.Snap.node_ref_key r0)
      by (intro Hk; apply Hni; rewrite <- Hk; exact Hin').
    unfold add_occ_fact; cbn [snd fst]. destruct (occ_expr_fact occ0) as [f0|].
    + rewrite GoIndex.nodekeymap_add_neq by (intro Hk; apply Hkr; symmetry; exact Hk).
      exact (IH Hnd' Hin).
    + exact (IH Hnd' Hin).
Qed.

(** MAP-LEVEL EXACTNESS: the fact stored at a visited ref's key is EXACTLY that occurrence's fact. *)
Lemma file_expr_facts_find {p} (fr : GoIndex.Snap.FileRef p) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (GoIndex.Snap.visit_file fr) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (file_expr_facts fr) = occ_expr_fact occ.
Proof.
  intro Hin. unfold file_expr_facts. apply fold_facts_find; [ apply visit_file_key_nodup | exact Hin ].
Qed.

(* ---- program-wide visit stream + fact map (§10 lifted to the whole program) ---- *)

Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite map_app, IH; reflexivity]. Qed.

Lemma nodup_app {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros H1 H2 Hd; [exact H2|].
  inversion H1 as [|? ? Hni Hnd]; subst. constructor.
  - rewrite in_app_iff. intros [Hin|Hin]; [ apply Hni; exact Hin | apply (Hd a); [left; reflexivity | exact Hin] ].
  - apply IH; [ exact Hnd | exact H2 | intros x Hx; apply Hd; right; exact Hx ].
Qed.

Lemma nodup_flat_map_tag {A B T} (g : A -> list B) (tag : B -> T) (key : A -> T) (l : list A) :
  (forall a, In a l -> NoDup (g a)) ->
  (forall a b, In a l -> In b (g a) -> tag b = key a) ->
  NoDup (map key l) ->
  NoDup (flat_map g l).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd Htag Hkey; [constructor|].
  inversion Hkey as [|? ? Hni Hkey' Heq]; subst.
  apply nodup_app.
  - apply Hnd; left; reflexivity.
  - apply IH; [ intros a' Ha'; apply Hnd; right; exact Ha'
              | intros a' b Ha' Hb; apply (Htag a' b); [right; exact Ha' | exact Hb]
              | exact Hkey' ].
  - intros x Hx1 Hx2.
    assert (Htx : tag x = key a) by (apply (Htag a x); [left; reflexivity | exact Hx1]).
    apply in_flat_map in Hx2. destruct Hx2 as [a' [Ha' Hb']].
    assert (Htx' : tag x = key a') by (apply (Htag a' x); [right; exact Ha' | exact Hb']).
    apply Hni. assert (Hka : key a = key a') by (rewrite <- Htx; exact Htx').
    rewrite Hka. apply in_map; exact Ha'.
Qed.

(** the visit stream of one file binding (empty for an unminted path — unreachable for a real binding). *)
Definition binding_visit (p : GoProgram) (b : FilePath * GoSourceFile)
  : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :=
  match GoIndex.Snap.file_of_path p (fst b) with
  | Some fr => GoIndex.Snap.visit_file fr
  | None => []
  end.

(** the WHOLE-PROGRAM visit stream: each file visited once, in canonical FileMap path order. *)
Definition prog_visit (p : GoProgram) : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :=
  flat_map (binding_visit p) (GoAST.file_bindings (prog_files p)).

(** every key in one binding's block has that binding's path (used for cross-file disjointness). *)
Lemma binding_visit_key_file : forall p b k,
  In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (binding_visit p b)) ->
  GoIndex.nk_file k = fst b.
Proof.
  intros p b k Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [| destruct Hin].
  apply in_map_iff in Hin. destruct Hin as [[r occ] [Hk Hin]]. cbn [fst] in Hk. subst k.
  rewrite GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf.
  exact (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef).
Qed.

(** program-wide keys are DISTINCT: distinct locals within a file, distinct paths across files. *)
Lemma prog_visit_key_nodup (p : GoProgram) :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (prog_visit p)).
Proof.
  unfold prog_visit. rewrite map_flat_map.
  apply (nodup_flat_map_tag
           (fun b => map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (binding_visit p b))
           GoIndex.nk_file (fun b => fst b) (GoAST.file_bindings (prog_files p))).
  - intros b _. unfold binding_visit.
    destruct (GoIndex.Snap.file_of_path p (fst b)); [ apply visit_file_key_nodup | constructor ].
  - intros b k _ Hin. exact (binding_visit_key_file p b k Hin).
  - apply GoAST.file_bindings_nodup_keys.
Qed.

Definition prog_expr_facts (p : GoProgram) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_visit p).

(** PROGRAM-LEVEL FACT EXACTNESS: the fact at a program-visited ref's key is EXACTLY that occurrence's fact. *)
Lemma prog_expr_facts_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_expr_facts p) = occ_expr_fact occ.
Proof.
  intro Hin. unfold prog_expr_facts. apply fold_facts_find; [ apply prog_visit_key_nodup | exact Hin ].
Qed.

(* ---- the EXPRESSION DECISION: every println argument resolves IFF the program is [ProgramTyped] ---- *)

Lemma forallb_flat_map {A B} (f : B -> bool) (g : A -> list B) (l : list A) :
  forallb f (flat_map g l) = forallb (fun x => forallb f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite forallb_app, IH; reflexivity]. Qed.

(** one file's argument occurrences resolve iff the file types (the §19 traversal projects [occs_file], reusing
    the C2 [occ_arg_typedb] = [source_file_typedb] bridge). *)
Lemma visit_file_arg_typedb {p} (fr : GoIndex.Snap.FileRef p) :
  forallb (fun x => GoTypes.occ_arg_typedb (snd x)) (GoIndex.Snap.visit_file fr)
  = source_file_typedb (GoIndex.Snap.file_ref_source fr).
Proof.
  rewrite GoTypes.forallb_map_snd, GoIndex.Snap.visit_file_snd, <- GoTypes.forallb_map_snd.
  apply GoTypes.occs_file_typedb_eq.
Qed.

(** the per-occurrence "argument resolves" check folded over the whole program. *)
Definition expr_all_ok (p : GoProgram) : bool :=
  forallb (fun x => GoTypes.occ_arg_typedb (snd x)) (prog_visit p).

(** DECISION EXACTNESS: [expr_all_ok] is EXACTLY [program_typedb] (hence [ProgramTyped]).  This is the
    expression half of [AnalysisOK <-> GoCompile]: no expression diagnostic <-> every argument resolves. *)
Lemma expr_all_ok_program_typedb (p : GoProgram) : expr_all_ok p = program_typedb p.
Proof.
  unfold expr_all_ok, prog_visit. rewrite forallb_flat_map. unfold program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_arg_typedb, Hsrc. reflexivity.
Qed.

Lemma expr_all_ok_ProgramTyped (p : GoProgram) : expr_all_ok p = true <-> GoTypes.ProgramTyped p.
Proof. rewrite expr_all_ok_program_typedb. apply GoTypes.program_typedb_iff. Qed.

(** [GoCompile p] IS whole-program admissibility: the program is typed through [GoTypes] AND every package
    has exactly one `main`.  The package clause is now SOURCE-owned (each file's [source_package]), rendered
    by [GoRender] — it is no longer a compiler-derived fact, so there is no [cf_pkg_name] / [CompilationFacts]
    record: the compiled evidence is exactly [ProgValid p].  Richer per-program facts (symbol/type tables)
    will decorate this same program later without a second AST; there is no unused placeholder now. *)
Definition GoCompile (p : GoProgram) : Prop := ProgValid p.

Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_ok      : GoCompile cp_program
}.

(** The compiled evidence EXPOSES that the same program is typed through [GoTypes] (§17): an immediate
    canonical projection, not a stored second copy of the typing proof. *)
Theorem compile_program_typed : forall p, GoCompile p -> ProgramTyped p.
Proof. intros p H; exact (proj1 H). Qed.

Theorem compilable_program_typed : forall cp : CompilableProgram, ProgramTyped (cp_program cp).
Proof. intro cp; exact (compile_program_typed _ (cp_ok cp)). Qed.

(** ---- the proof-producing executable compiler ---- *)

Inductive CompileError : Type :=
| ErrTyping           (* some declaration fails typing: a constant outside every representable range, a
                         float or complex-component overflow, a fractional-or-out-of-range float/complex->integer,
                         a nonzero-imaginary complex->scalar, a wrong-type operand, or an invalid (nested)
                         conversion — the one honest typing error now that typing can fail for several reasons *)
| ErrPackageMainCount (* some package has zero or multiple `main` declarations *).

Inductive result (E A : Type) : Type := Ok : A -> result E A | Err : E -> result E A.
Arguments Ok {E A}. Arguments Err {E A}.

Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

Definition go_compile (p : GoProgram) : result CompileError CompilableProgram :=
  match bool_sumbool (prog_ok p) with
  | left H  => Ok (mkCompilable p (proj1 (prog_ok_iff p) H))
  | right _ =>
      (* the whole program is typed but some package's `main` count is wrong, vs. a typing failure
         (a constant fitting no integer type, a non-integer conversion operand, or an invalid nested
         conversion). *)
      if program_typedb p then Err ErrPackageMainCount else Err ErrTyping
  end.

(** (A) internal exactness: [go_compile] accepts exactly the admissible programs, whole-program. *)
Theorem go_compile_sound : forall p cp,
  go_compile p = Ok cp -> cp_program cp = p /\ GoCompile (cp_program cp).
Proof.
  intros p cp Heq. split; [ | exact (cp_ok cp) ].
  revert Heq. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H | H ].
  - intro Heq; injection Heq as <-; reflexivity.
  - destruct (program_typedb p); discriminate.
Qed.

Theorem go_compile_complete : forall p,
  GoCompile p -> exists cp, go_compile p = Ok cp.
Proof.
  intros p Hvalid. apply (proj2 (prog_ok_iff p)) in Hvalid. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H' | H' ]; [ eexists; reflexivity | ].
  rewrite Hvalid in H'; discriminate.
Qed.

(** A rejected program yields no CompilableProgram (and hence no SafeProgram, no image). *)
Lemma reject_no_compile : forall p, prog_ok p = false -> ~ GoCompile p.
Proof.
  intros p E Hvalid. apply (proj2 (prog_ok_iff p)) in Hvalid.
  rewrite Hvalid in E; discriminate.
Qed.

(** ---- §8 ORDER-INDEPENDENCE of admissibility: [GoCompile] / [go_compile] depend only on the file MAP,
    never on construction order (typing respects the map by [ProgramTyped_Equal]; the package summaries
    respect it by [package_summaries_Equal]). ---- *)

Theorem GoCompile_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> GoCompile p1 -> GoCompile p2.
Proof.
  intros p1 p2 Heq [Ht Hall]. split.
  - exact (ProgramTyped_Equal p1 p2 Heq Ht).
  - intros dir s Hmt. apply (Hall dir s). apply PMF.find_mapsto_iff.
    rewrite (package_summaries_Equal (prog_files p1) (prog_files p2) Heq dir).
    apply PMF.find_mapsto_iff. exact Hmt.
Qed.

Theorem prog_ok_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> prog_ok p1 = prog_ok p2.
Proof.
  intros p1 p2 Heq.
  destruct (prog_ok p1) eqn:E1; destruct (prog_ok p2) eqn:E2; try reflexivity.
  - apply (proj1 (prog_ok_iff p1)) in E1. apply (GoCompile_Equal p1 p2 Heq) in E1.
    apply (proj2 (prog_ok_iff p2)) in E1. rewrite E1 in E2; discriminate.
  - apply (proj1 (prog_ok_iff p2)) in E2. apply (GoCompile_Equal p2 p1 (GoAST.FilesEqual_sym _ _ Heq)) in E2.
    apply (proj2 (prog_ok_iff p1)) in E2. rewrite E2 in E1; discriminate.
Qed.

(** the [go_compile] RESULT CLASS (accept vs. which error) — invariant under file insertion order. *)
Definition go_compile_class (p : GoProgram) : result CompileError unit :=
  match go_compile p with Ok _ => Ok tt | Err e => Err e end.

Lemma go_compile_class_spec : forall p,
  go_compile_class p
  = (if prog_ok p then Ok tt else if program_typedb p then Err ErrPackageMainCount else Err ErrTyping).
Proof.
  intro p. unfold go_compile_class, go_compile.
  destruct (bool_sumbool (prog_ok p)) as [H|H]; rewrite H; [ reflexivity | ].
  destruct (program_typedb p); reflexivity.
Qed.

Theorem go_compile_class_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> go_compile_class p1 = go_compile_class p2.
Proof.
  intros p1 p2 Heq. rewrite !go_compile_class_spec.
  rewrite (prog_ok_Equal p1 p2 Heq), (program_typedb_Equal p1 p2 Heq). reflexivity.
Qed.

Theorem go_compile_class_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  go_compile_class p1 = go_compile_class p2.
Proof.
  intros ms n1 n2 p1 p2 Hperm Hb1 Hb2. apply go_compile_class_Equal.
  unfold build_program in *.
  destruct (filemap_of_nodes n1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes n2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation n1 n2 fm1 fm2 Hperm F1 F2).
Qed.

(** The empty program (empty file MAP) is accepted: no package to type and no `main` to count, so [prog_ok]
    holds vacuously (the file map's elements and the package map are both empty). *)
Lemma prog_ok_empty : forall ms, prog_ok (empty_program ms) = true.
Proof. intro ms. vm_compute. reflexivity. Qed.

(** ---- boundary fixture: an out-of-range argument rejects the WHOLE program BEFORE any emission ---- *)

(** A single-file program whose only `println` argument is [int_max + 1] (one past the one [Ints] upper
    bound; NOT a duplicated numeric literal) — unrepresentable as the default [TInteger IInt] through the
    [GoTypes] authority. *)
Definition over_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt (Z.to_N (int_max + 1)) ] ] ].

(* the whole program fails typing, so [prog_ok] rejects it and [go_compile] returns the honest typing
   error — and there is NO [CompilableProgram] for it (hence no [SafeProgram], no [DirectoryImage], no
   rendering/emission): rejection happens strictly in Rocq, before any bytes. *)
Example over_program_untyped   : program_typedb over_program = false.        Proof. vm_compute; reflexivity. Qed.
Example over_program_not_ok    : prog_ok over_program = false.               Proof. vm_compute; reflexivity. Qed.
Example over_program_rejected  : go_compile over_program = Err ErrTyping.    Proof. vm_compute; reflexivity. Qed.
Example over_program_no_compile : ~ GoCompile over_program.
Proof. exact (reject_no_compile over_program over_program_not_ok). Qed.

(** ---- integer-family programs (§12/§20): a concrete accepted integer program compiles; an invalid nested
    conversion rejects the WHOLE program with the same honest typing error, before any bytes. ---- *)
Definition int_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IInt8 (EInt 127)
                       ; EIntConvert IUint64 (EInt 18446744073709551615)
                       ; EIntConvert IInt8 (EIntConvert IInt16 (EInt 127)) ] ] ].
Example int_program_typed    : program_typedb int_program = true. Proof. vm_compute; reflexivity. Qed.
Example int_program_ok       : prog_ok int_program = true.        Proof. vm_compute; reflexivity. Qed.
Example int_program_compiles : exists cp, go_compile int_program = Ok cp.
Proof. eexists; reflexivity. Qed.

(** A program whose only argument is [uint8(int(300))] — a valid inner [int(300)] whose value does NOT fit
    the outer [uint8]; the invalid nested conversion cannot be revived, so the whole program is rejected. *)
Definition bad_convert_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IUint8 (EIntConvert IInt (EInt 300)) ] ] ].
Example bad_convert_untyped     : program_typedb bad_convert_program = false. Proof. vm_compute; reflexivity. Qed.
Example bad_convert_rejected    : go_compile bad_convert_program = Err ErrTyping. Proof. vm_compute; reflexivity. Qed.
Example bad_convert_no_compile  : ~ GoCompile bad_convert_program.
Proof. exact (reject_no_compile bad_convert_program eq_refl). Qed.

(** ---- a concrete STRING program is whole-program admissible (§25): a single `main` whose `println`
    mixes a string literal with a bool and an int is typed and compiles to a [CompilableProgram]. ---- *)
Definition str_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EString "hello"; EBool true; EInt 7 ] ] ].
Example str_program_typed    : program_typedb str_program = true. Proof. vm_compute; reflexivity. Qed.
Example str_program_ok       : prog_ok str_program = true.        Proof. vm_compute; reflexivity. Qed.
Example str_program_compiles : exists cp, go_compile str_program = Ok cp.
Proof. eexists; reflexivity. Qed.

(** ---- float programs (§38): a concrete accepted float program (a bare float64, an explicit float32
    conversion, and an exact float->int conversion) compiles to a [CompilableProgram]; a fractional
    float->int conversion rejects the WHOLE program with the honest typing error, before any bytes — and there
    is NO [CompilableProgram] for it. ---- *)
Definition float_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EFloat (mkDecimal 15 (-1) eq_refl)
                       ; EFloatConvert F32 (EFloat (mkDecimal 15 (-1) eq_refl))
                       ; EIntConvert IInt (EFloat (mkDecimal 3 0 eq_refl)) ] ] ].
Example float_program_typed    : program_typedb float_program = true. Proof. vm_compute. reflexivity. Qed.
Example float_program_ok       : prog_ok float_program = true.        Proof. vm_compute. reflexivity. Qed.
Example float_program_compiles : exists cp, go_compile float_program = Ok cp.
Proof. eexists; reflexivity. Qed.

Definition float_reject_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IInt (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ].   (* int(3.5): fractional *)
Example float_reject_untyped    : program_typedb float_reject_program = false. Proof. vm_compute. reflexivity. Qed.
Example float_reject_rejected   : go_compile float_reject_program = Err ErrTyping.
Proof. vm_compute. reflexivity. Qed.
Example float_reject_no_compile : ~ GoCompile float_reject_program.
Proof. apply (reject_no_compile float_reject_program); vm_compute; reflexivity. Qed.

(** ---- §50 a whole COMPLEX program (bare complex default, complex64/complex128 conversions, a scalar->
    complex conversion, and a zero-imaginary complex->scalar conversion) is typed and compiles; a component-
    overflow program and a nonzero-imaginary complex->int program are ordinary [ErrTyping] rejections with no
    [CompilableProgram]. ---- *)
Definition complex_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal (-25) (-1) eq_refl))
                       ; EComplexConvert C64  (EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal 0 0 eq_refl)))
                       ; EComplexConvert C128 (EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal 0 0 eq_refl)))
                       ; EComplexConvert C64  (EInt 1)
                       ; EIntConvert IInt (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 0 0 eq_refl))) ] ] ].
Example complex_program_typed    : program_typedb complex_program = true. Proof. vm_compute. reflexivity. Qed.
Example complex_program_ok       : prog_ok complex_program = true.        Proof. vm_compute. reflexivity. Qed.
Example complex_program_compiles : exists cp, go_compile complex_program = Ok cp.
Proof. eexists; reflexivity. Qed.

Definition complex_overflow_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EComplexConvert C64 (EComplex (mkDC (mkDecimal 1 39 eq_refl) (mkDecimal 0 0 eq_refl))) ] ] ].
Example complex_overflow_untyped    : program_typedb complex_overflow_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_overflow_rejected   : go_compile complex_overflow_program = Err ErrTyping. Proof. vm_compute. reflexivity. Qed.
Example complex_overflow_no_compile : ~ GoCompile complex_overflow_program.
Proof. apply (reject_no_compile complex_overflow_program); vm_compute; reflexivity. Qed.

Definition complex_nonzero_imag_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IInt (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 1 0 eq_refl))) ] ] ].
Example complex_nonzero_imag_untyped    : program_typedb complex_nonzero_imag_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_rejected   : go_compile complex_nonzero_imag_program = Err ErrTyping. Proof. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_no_compile : ~ GoCompile complex_nonzero_imag_program.
Proof. apply (reject_no_compile complex_nonzero_imag_program); vm_compute; reflexivity. Qed.
