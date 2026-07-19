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
   §17 (C3 FINAL) — ERASED cross-snapshot reports.  A [DiagnosticReason p] is indexed by the snapshot [p], so
   two snapshots' diagnostics have DIFFERENT dependent types.  [erase_diagnostic] projects a reason to a
   snapshot-INDEPENDENT [ErasedDiagnostic] (code + erased anchors carrying only NodeKey / FilePath /
   package-string identity + a STABLE payload — the conversion/default-target [GoType], NO source syntax), so
   reports from two snapshots are compared by plain [=] on erased values, never an unsafe dependent transport.
   The exact source expression stays reachable through the original typed anchor WHILE inside one [p].
   ============================================================================================================ *)

Inductive ErasedAnchor : Type :=
| EANode    : GoIndex.NodeKey -> ErasedAnchor
| EAFile    : FilePath -> ErasedAnchor
| EAPackage : string -> ErasedAnchor
| EAProgram : ErasedAnchor.

Definition erase_anchor {p} (a : DiagnosticAnchor p) : ErasedAnchor :=
  match a with
  | AtNode r     => EANode (GoIndex.Snap.node_ref_key r)
  | AtFile fr    => EAFile (GoIndex.Snap.file_ref_path fr)
  | AtPackage pk => EAPackage (package_ref_key pk)
  | AtProgram    => EAProgram
  end.

Record ErasedDiagnostic : Type := mkErasedDiagnostic {
  ed_code    : DiagnosticCode ;
  ed_primary : ErasedAnchor ;
  ed_related : list ErasedAnchor ;
  ed_target  : option GoType
}.

(* the STABLE erased payload: the conversion TARGET / default target [GoType] where the reason carries one —
   NO source expression (the exact operand stays reachable through the typed anchor inside one [p]). *)
Definition erased_target {p} (d : DiagnosticReason p) : option GoType :=
  match d with
  | DRInvalidConversion _ _ t _      => Some t
  | DRDefaultNotRepresentable _ _ dt => Some dt
  | DRDuplicateMain _ _              => None
  | DRMissingMain _                  => None
  end.

Definition erase_diagnostic {p} (d : DiagnosticReason p) : ErasedDiagnostic :=
  mkErasedDiagnostic (diagnostic_code d) (erase_anchor (diagnostic_primary d))
    (map erase_anchor (diagnostic_related d)) (erased_target d).

(* intra-snapshot preservation: erasing keeps the CODE, the primary anchor's KEY identity, and the related
   anchors AS A MAP (so their canonical order is preserved). *)
Lemma erase_diagnostic_code {p} (d : DiagnosticReason p) : ed_code (erase_diagnostic d) = diagnostic_code d.
Proof. reflexivity. Qed.

Lemma erase_diagnostic_primary {p} (d : DiagnosticReason p) :
  ed_primary (erase_diagnostic d) = erase_anchor (diagnostic_primary d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related {p} (d : DiagnosticReason p) :
  ed_related (erase_diagnostic d) = map erase_anchor (diagnostic_related d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related_length {p} (d : DiagnosticReason p) :
  length (ed_related (erase_diagnostic d)) = length (diagnostic_related d).
Proof.
  cbn [ed_related erase_diagnostic].
  induction (diagnostic_related d) as [|x xs IH]; cbn [map length]; [ reflexivity | rewrite IH; reflexivity ].
Qed.

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

(** the RETAINED per-file visit blocks: each file's stream, visited ONCE, in canonical FileMap path order.
    [analyze_indexed] retains this and derives BOTH the flattened analysis stream ([prog_visit] = [concat])
    AND the enclosing-context annotations ([annotate_program]) from it — one [Snap.visit_file] per file. *)
Definition prog_blocks (p : GoProgram) : list (list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :=
  map (binding_visit p) (GoAST.file_bindings (prog_files p)).

(** the WHOLE-PROGRAM visit stream: the retained blocks flattened (each file visited once, path order). *)
Definition prog_visit (p : GoProgram) : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :=
  concat (prog_blocks p).

(** the flattened stream IS the per-binding flat_map (used by the existing membership/fold proofs). *)
Lemma prog_visit_flat_map (p : GoProgram) :
  prog_visit p = flat_map (binding_visit p) (GoAST.file_bindings (prog_files p)).
Proof. unfold prog_visit, prog_blocks. rewrite flat_map_concat_map. reflexivity. Qed.

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
  rewrite prog_visit_flat_map, map_flat_map.
  apply (nodup_flat_map_tag
           (fun b => map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (binding_visit p b))
           GoIndex.nk_file (fun b => fst b) (GoAST.file_bindings (prog_files p))).
  - intros b _. unfold binding_visit.
    destruct (GoIndex.Snap.file_of_path p (fst b)); [ apply visit_file_key_nodup | constructor ].
  - intros b k _ Hin. exact (binding_visit_key_file p b k Hin).
  - apply GoAST.file_bindings_nodup_keys.
Qed.

(* [prog_expr_facts] is defined below as the SINGLE-PASS fold reading [prog_status_map] (no per-occurrence
   [const_info]); [add_occ_fact] above is its per-node SPECIFICATION, used only to state exactness. *)


(* the occurrence status map + its exactness are built below as ONE fold over the delivered visit stream
   ([prog_status_map] / [prog_status_map_find] / [prog_status_map_find_operand]), replacing the former
   [file_statuses] source recursion. *)

(* ---- OPERAND ADJACENCY: a conversion occurrence at [me] has its operand occurrence at [Pos.succ me] (the
   index's canonical child id), so a conversion's operand status is read from [prog_status_map] at the operand
   key — no [const_info] rescan of the operand subtree. ---- *)

Lemma occs_expr_head_ex : forall e parent role start,
  exists occ, In (start, occ) (GoIndex.occs_expr parent role start e) /\ GoIndex.view_expr occ = Some e.
Proof. intros e parent role start; destruct e; cbn [GoIndex.occs_expr]; eexists; (split; [left; reflexivity|reflexivity]). Qed.

Lemma occs_expr_operand : forall e parent role start me occ ce x,
  In (me, occ) (GoIndex.occs_expr parent role start e) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_expr parent role start e) /\ GoIndex.view_expr occ' = Some x.
Proof.
  induction e as [ b|n1|n2|s| it y IHy | df | ft y IHy | dcx | ct y IHy ]; intros parent role start me occ ce x Hin Hv Hc.
  (* leaves: the only occurrence is the leaf, whose view has no expr_child *)
  1,2,3,4,6,8: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
               injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
               injection Hv as Hce; subst ce; cbn [expr_child] in Hc; discriminate Hc.
  (* conversions: head is the conversion (operand at [Pos.succ me]); tail is the operand subtree (IH) *)
  all: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hin];
    [ injection Heq as Hid Hocc; rewrite <- Hid; rewrite <- Hocc in Hv;
      cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; injection Hv as Hce; subst ce;
      cbn [expr_child] in Hc; injection Hc as Hx; subst x;
      destruct (occs_expr_head_ex y start GoIndex.RConversionOperand (Pos.succ start)) as [occ' [Hin' Hv']];
      exists occ'; split; [right; exact Hin' | exact Hv']
    | destruct (IHy start GoIndex.RConversionOperand (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']];
      exists occ'; split; [right; exact Hin' | exact Hv'] ].
Qed.

Lemma in_app_operand {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ x :
  (forall M O ce X, In (M, O) L1 -> GoIndex.view_expr O = Some ce -> expr_child ce = Some X ->
     exists O', In (Pos.succ M, O') L1 /\ GoIndex.view_expr O' = Some X) ->
  (forall M O ce X, In (M, O) L2 -> GoIndex.view_expr O = Some ce -> expr_child ce = Some X ->
     exists O', In (Pos.succ M, O') L2 /\ GoIndex.view_expr O' = Some X) ->
  forall ce, In (me, occ) (L1 ++ L2) -> GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (L1 ++ L2) /\ GoIndex.view_expr occ' = Some x.
Proof.
  intros H1 H2 ce Hin Hv Hc. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; left; exact Hin' | exact Hv'].
  - destruct (H2 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; right; exact Hin' | exact Hv'].
Qed.

Lemma occs_args_operand : forall es parent aidx start me occ ce x,
  In (me, occ) (GoIndex.occs_args parent aidx start es) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_args parent aidx start es) /\ GoIndex.view_expr occ' = Some x.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_args] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. unfold GoIndex.occs_arg. eapply occs_expr_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_stmt_operand : forall s parent sidx start me occ ce x,
  In (me, occ) (GoIndex.occs_stmt parent sidx start s) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_stmt parent sidx start s) /\ GoIndex.view_expr occ' = Some x.
Proof.
  intros [args] parent sidx start me occ ce x Hin Hv Hc. cbn [GoIndex.occs_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_args_operand args start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_stmts_operand : forall ss parent sidx start me occ ce x,
  In (me, occ) (GoIndex.occs_stmts parent sidx start ss) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_stmts parent sidx start ss) /\ GoIndex.view_expr occ' = Some x.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_stmts] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occs_stmt_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_decl_operand : forall d parent didx start me occ ce x,
  In (me, occ) (GoIndex.occs_decl parent didx start d) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_decl parent didx start d) /\ GoIndex.view_expr occ' = Some x.
Proof.
  intros [body] parent didx start me occ ce x Hin Hv Hc. cbn [GoIndex.occs_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_stmts_operand body start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_decls_operand : forall ds parent didx start me occ ce x,
  In (me, occ) (GoIndex.occs_decls parent didx start ds) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_decls parent didx start ds) /\ GoIndex.view_expr occ' = Some x.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_decls] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occs_decl_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_file_operand : forall f me occ ce x,
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_file f) /\ GoIndex.view_expr occ' = Some x.
Proof.
  intros f me occ ce x Hin Hv Hc. unfold GoIndex.occs_file in *.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_decls_operand (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ ce x Hin Hv Hc)
      as [occ' [Hin' Hv']].
    exists occ'. split; [right; right; exact Hin' | exact Hv'].
Qed.

(* ============================================================================================================
   §10 (C3) — EXPRESSION-FACT TOTALITY GROUNDWORK.  On a TYPED program every visited expression occurrence has a
   successful [const_info] (hence an exact fact).  Three facts compose it: a typed println argument's
   [const_info] SUCCEEDS ([expr_typedb_const_info]); [const_info]'s recursion propagates success DOWNWARD to
   every conversion operand ([const_info_child_some], lifted structurally through the occurrence enumeration);
   and the whole-file / whole-program traversal visits exactly those subexpressions.  So on [ProgramTyped]
   every visited expression occurrence's [const_info] is [Some] — the fact query is TOTAL.
   ============================================================================================================ *)

(* a typed argument's constant status succeeds (its whole conversion chain is representable). *)
Lemma expr_typedb_const_info : forall u e, GoTypes.expr_typedb u e = true -> exists ci, const_info e = Some ci.
Proof.
  intros u e H. unfold GoTypes.expr_typedb in H.
  destruct (GoTypes.resolve_expr u e) as [t|] eqn:Hr; [|discriminate H].
  unfold GoTypes.resolve_expr in Hr.
  destruct (GoTypes.resolve_expr_const u e) as [rc|] eqn:Hrc; cbn [option_map] in Hr; [|discriminate Hr].
  destruct (GoTypes.resolve_expr_const_sound u e rc Hrc) as [ci [Hci _]]. exists ci; exact Hci.
Qed.

(* one downward step: a node whose [const_info] succeeds has an expression child whose [const_info] succeeds. *)
Lemma const_info_child_some : forall e x ci,
  expr_child e = Some x -> const_info e = Some ci -> exists cix, const_info x = Some cix.
Proof.
  intros e x ci Hc Hci. rewrite const_info_step_reflect, Hc in Hci.
  destruct e as [ b|n1|n2|s| it y | df | ft y | dcx | ct y ]; cbn [expr_child] in Hc; try discriminate Hc;
    cbn [GoTypes.const_info_step] in Hci;
    (destruct (const_info x) as [cix|]; [ exists cix; reflexivity | discriminate Hci ]).
Qed.

(* the const_info of EVERY occurrence in [occs_expr ... e] is [Some], given [const_info e] is: leaves view [e]
   itself; a conversion's head is [e] (Some given), and its operand subtree inherits Some by [const_info_child_some]. *)
Lemma occs_expr_const_info_some : forall e parent role pos me occ e' ci,
  const_info e = Some ci ->
  In (me, occ) (GoIndex.occs_expr parent role pos e) ->
  GoIndex.view_expr occ = Some e' -> exists ci', const_info e' = Some ci'.
Proof.
  induction e as [ b|n1|n2|s| it y IHy | df | ft y IHy | dcx | ct y IHy ];
    intros parent role pos me occ e' ci Hci Hin Hv.
  1,2,3,4,6,8: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|[]];
    injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
    injection Hv as <-; exists ci; exact Hci.
  all: (cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hin];
    [ injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
      injection Hv as <-; exists ci; exact Hci
    | assert (Hy : exists ciy, const_info y = Some ciy)
        by (cbn [const_info] in Hci; destruct (const_info y) as [ciy|];
            [ eexists; reflexivity | discriminate Hci ]);
      destruct Hy as [ciy Hciy];
      exact (IHy pos GoIndex.RConversionOperand (Pos.succ pos) me occ e' ciy Hciy Hin Hv) ]).
Qed.

Lemma in_app_const_info_some {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ e' :
  (forall M O E, In (M, O) L1 -> GoIndex.view_expr O = Some E -> exists ci, const_info E = Some ci) ->
  (forall M O E, In (M, O) L2 -> GoIndex.view_expr O = Some E -> exists ci, const_info E = Some ci) ->
  In (me, occ) (L1 ++ L2) -> GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    [ exact (H1 me occ e' Hin Hv) | exact (H2 me occ e' Hin Hv) ].
Qed.

Lemma occs_arg_const_info_some : forall e parent aidx pos me occ e',
  GoTypes.expr_typedb GoTypes.UsePrintlnArg e = true ->
  In (me, occ) (GoIndex.occs_arg parent aidx pos e) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros e parent aidx pos me occ e' Ht Hin Hv. unfold GoIndex.occs_arg in Hin.
  destruct (expr_typedb_const_info GoTypes.UsePrintlnArg e Ht) as [ci Hci].
  exact (occs_expr_const_info_some e parent (GoIndex.RPrintlnArg aidx) pos me occ e' ci Hci Hin Hv).
Qed.

Lemma occs_args_const_info_some : forall es parent aidx pos me occ e',
  forallb (GoTypes.expr_typedb GoTypes.UsePrintlnArg) es = true ->
  In (me, occ) (GoIndex.occs_args parent aidx pos es) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction es as [|e rest IH]; intros parent aidx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_args] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hte Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_arg_const_info_some e parent aidx pos M O E Hte HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S aidx) (Pos.succ (GoIndex.end_expr pos e)) M O E Htr HinM HvM).
Qed.

Lemma occs_stmt_const_info_some : forall s parent sidx pos me occ e',
  GoTypes.stmt_typedb s = true ->
  In (me, occ) (GoIndex.occs_stmt parent sidx pos s) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros [args] parent sidx pos me occ e' Ht Hin Hv. cbn [GoIndex.occs_stmt] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - cbn [GoTypes.stmt_typedb] in Ht.
    exact (occs_args_const_info_some args pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occs_stmts_const_info_some : forall ss parent sidx pos me occ e',
  forallb GoTypes.stmt_typedb ss = true ->
  In (me, occ) (GoIndex.occs_stmts parent sidx pos ss) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction ss as [|s rest IH]; intros parent sidx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_stmts] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hts Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_stmt_const_info_some s parent sidx pos M O E Hts HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S sidx) (Pos.succ (GoIndex.end_stmt pos s)) M O E Htr HinM HvM).
Qed.

Lemma occs_decl_const_info_some : forall d parent didx pos me occ e',
  GoTypes.decl_typedb d = true ->
  In (me, occ) (GoIndex.occs_decl parent didx pos d) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros [body] parent didx pos me occ e' Ht Hin Hv. cbn [GoIndex.occs_decl] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - cbn [GoTypes.decl_typedb] in Ht.
    exact (occs_stmts_const_info_some body pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occs_decls_const_info_some : forall ds parent didx pos me occ e',
  forallb GoTypes.decl_typedb ds = true ->
  In (me, occ) (GoIndex.occs_decls parent didx pos ds) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction ds as [|d rest IH]; intros parent didx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_decls] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Htd Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_decl_const_info_some d parent didx pos M O E Htd HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S didx) (Pos.succ (GoIndex.end_decl pos d)) M O E Htr HinM HvM).
Qed.

Lemma occs_file_const_info_some : forall f me occ e',
  GoTypes.source_file_typedb f = true ->
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros f me occ e' Ht Hin Hv. unfold GoIndex.occs_file in Hin.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - unfold GoTypes.source_file_typedb, GoTypes.file_typedb in Ht.
    exact (occs_decls_const_info_some (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ e' Ht Hin Hv).
Qed.

(* the WHOLE-PROGRAM statement: on [program_typedb] every visited expression occurrence's [const_info] is [Some]. *)
Lemma prog_visit_const_info_some (p : GoProgram) :
  GoTypes.program_typedb p = true ->
  forall r occ e', In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros Hpt r occ e' Hin Hv. rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin.
  destruct Hin as [b [Hb Hrb]]. unfold binding_visit in Hrb.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc_at : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc_at.
  unfold GoTypes.program_typedb in Hpt.
  pose proof (proj1 (forallb_forall (fun b => GoTypes.source_file_typedb (snd b))
                (GoAST.file_bindings (prog_files p))) Hpt b Hb) as Htb.
  cbv beta in Htb.
  assert (Hsrceq : snd b = GoIndex.Snap.file_ref_source fr).
  { pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfb.
    pose proof (GoIndex.Snap.file_of_path_source_exact p (fst b) fr Ef) as Hfe.
    rewrite Hfb in Hfe. injection Hfe as Heq; exact Heq. }
  rewrite Hsrceq in Htb.
  exact (occs_file_const_info_some (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ e' Htb Hsrc_at Hv).
Qed.

(* a NodeRef is ALWAYS visited (its file is represented, and [visit_file] is complete over the file). *)
Lemma noderef_in_prog_visit (p : GoProgram) (r : GoIndex.Snap.NodeRef p) :
  In (r, GoIndex.Snap.source_occurrence_of_ref r) (prog_visit p).
Proof.
  pose proof (GoIndex.Snap.file_of_path_complete p (GoIndex.Snap.node_ref_file r)) as Hcomp.
  pose proof (GoIndex.Snap.file_of_path_source_exact p
                (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r))
                (GoIndex.Snap.node_ref_file r) Hcomp) as Hfind.
  pose proof (GoAST.find_file_bindings (prog_files p)
                (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r))
                (GoIndex.Snap.file_ref_source (GoIndex.Snap.node_ref_file r)) Hfind) as Hin_b.
  rewrite prog_visit_flat_map. apply in_flat_map.
  exists (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r),
          GoIndex.Snap.file_ref_source (GoIndex.Snap.node_ref_file r)).
  split; [exact Hin_b|]. unfold binding_visit; cbn [fst].
  rewrite Hcomp. apply GoIndex.Snap.visit_file_complete. reflexivity.
Qed.

(* ============================================================================================================
   §14 (C3) — the OCCURRENCE STATUS MAP as a fold over the DELIVERED visit stream (no separate source recursion).
   [operand_key r] is the canonical child (operand) key of a conversion at [r] (same file, [Pos.succ local]).  The one
   bottom-up pass ([status_step], folded right-to-left over the preorder [prog_visit]) stores each expression
   occurrence's [const_info] via ONE [const_info_step], reading its operand's status at [operand_key] from the
   ALREADY-FOLDED tail (the operand is a LATER preorder node, so it was folded first).
   ============================================================================================================ *)

Definition operand_key {p} (r : GoIndex.Snap.NodeRef p) : GoIndex.NodeKey :=
  GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (GoIndex.Snap.node_ref_local r)).

(* the operand of a visited conversion is ITSELF a visited occurrence whose key is [operand_key] and whose view is the
   operand expression (minted through the index from its exact local id). *)
Lemma prog_visit_operand (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
  exists r', In (r', GoIndex.Snap.source_occurrence_of_ref r') (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r' = operand_key r
    /\ GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref r') = Some x.
Proof.
  intros Hin Hv Hc.
  rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc.
  destruct (occs_file_operand (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ e x Hsrc Hv Hc)
    as [occ' [Hin' Hvx]].
  apply GoIndex.occs_file_exact in Hin'.
  assert (Hvalid : GoIndex.valid_localb (GoIndex.Snap.file_ref_source fr) (Pos.succ (GoIndex.Snap.node_ref_local r)) = true).
  { unfold GoIndex.valid_localb.
    rewrite (GoIndex.source_occurrence_meta (GoIndex.Snap.file_ref_source fr)
               (Pos.succ (GoIndex.Snap.node_ref_local r)) occ' Hin'). reflexivity. }
  pose proof (GoIndex.Snap.file_of_path_source_exact p (fst b) fr Ef) as Hfind.
  pose proof (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef) as Hpath.
  assert (Hfind' : GoAST.find_file (GoIndex.Snap.file_ref_path fr) (prog_files p) = Some (GoIndex.Snap.file_ref_source fr))
    by (rewrite Hpath; exact Hfind).
  destruct (GoIndex.Snap.ref_of_key_source p (GoIndex.indexed_syntax (GoIndex.index_program p))
              (GoIndex.Snap.file_ref_path fr) (GoIndex.Snap.file_ref_source fr)
              (Pos.succ (GoIndex.Snap.node_ref_local r)) Hfind' Hvalid) as [r' [Hrok [Hrlocal Hrsrc]]].
  exists r'.
  assert (Hkey : GoIndex.Snap.node_ref_key r' = operand_key r).
  { pose proof (GoIndex.Snap.ref_of_key_sound p (GoIndex.indexed_syntax (GoIndex.index_program p)) _ r' Hrok) as Hk.
    rewrite Hk. unfold operand_key. rewrite GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file]. rewrite Hfile. reflexivity. }
  assert (Hsor : GoIndex.Snap.source_occurrence_of_ref r' = occ').
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r') as Hso'.
    rewrite Hrlocal, Hrsrc in Hso'.
    rewrite Hin' in Hso'. injection Hso' as ->. reflexivity. }
  split; [ | split ].
  - apply noderef_in_prog_visit.
  - exact Hkey.
  - rewrite Hsor; exact Hvx.
Qed.

(* the one bottom-up step: a non-expression occurrence contributes nothing; an expression occurrence stores its
   [const_info] computed by ONE [const_info_step], reading its operand's status at [operand_key] from the accumulator. *)
Definition psm_step {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t (option ConstInfo)) : GoIndex.NodeKeyMapBase.t (option ConstInfo) :=
  match GoIndex.view_expr (snd ro) with
  | None => m
  | Some e =>
      GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (fst ro))
        (GoTypes.const_info_step e
           match expr_child e with
           | Some _ => match GoIndex.NodeKeyMapBase.find (operand_key (fst ro)) m with Some s => s | None => None end
           | None => None
           end) m
  end.

Definition prog_status_map (p : GoProgram) : GoIndex.NodeKeyMapBase.t (option ConstInfo) :=
  fold_right psm_step (GoIndex.NodeKeyMapBase.empty (option ConstInfo)) (prog_visit p).

(* the fold's find at a visited expression occurrence's key is EXACTLY its [const_info]: for a leaf,
   [const_info_step] ignores the (absent) child; for a conversion, the operand — a LATER preorder node, so it is
   in the ALREADY-FOLDED tail [l2] (the [OperandClosed] hypothesis) — has its own exact status by the induction
   hypothesis, and [const_info_step_reflect] recombines it into the node's [const_info].  Keys are distinct
   (NoDup), so no later add disturbs an earlier occurrence's stored status. *)
Lemma psm_fold_find {p} (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) L) ->
  (forall l1 r occ l2, L = l1 ++ (r, occ) :: l2 ->
     forall e x, GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
     exists r' occ', GoIndex.Snap.node_ref_key r' = operand_key r /\ GoIndex.view_expr occ' = Some x /\ In (r', occ') l2) ->
  forall r occ e, In (r, occ) L -> GoIndex.view_expr occ = Some e ->
    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r)
      (fold_right psm_step (GoIndex.NodeKeyMapBase.empty (option ConstInfo)) L) = Some (const_info e).
Proof.
  induction L as [|[r0 occ0] t IH]; intros Hnd Hoc r occ e Hin Hv; [ destruct Hin |].
  cbn [map fst] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  assert (Hoct : forall l1 r' occ' l2, t = l1 ++ (r', occ') :: l2 ->
     forall e' x, GoIndex.view_expr occ' = Some e' -> expr_child e' = Some x ->
     exists r'' occ'', GoIndex.Snap.node_ref_key r'' = operand_key r' /\ GoIndex.view_expr occ'' = Some x /\ In (r'', occ'') l2).
  { intros l1 r' occ' l2 Ht e' x Hv' Hc'.
    refine (Hoc ((r0, occ0) :: l1) r' occ' l2 _ e' x Hv' Hc').
    cbn [app]; rewrite Ht; reflexivity. }
  cbn [fold_right].
  destruct Hin as [Heq|Hin].
  - injection Heq as Hr0 Hocc0; subst r0; subst occ0.
    unfold psm_step at 1; cbn [fst snd]. rewrite Hv, GoIndex.nodekeymap_add_eq. f_equal.
    rewrite (GoTypes.const_info_step_reflect e).
    destruct (expr_child e) as [x|] eqn:Ec.
    + destruct (Hoc [] r occ t eq_refl e x Hv Ec) as [r' [occ' [Hk [Hvx Hin']]]].
      rewrite <- Hk, (IH Hnd' Hoct r' occ' x Hin' Hvx). reflexivity.
    + reflexivity.
  - unfold psm_step at 1; cbn [fst snd].
    destruct (GoIndex.view_expr occ0) as [e0|] eqn:Hv0.
    + rewrite GoIndex.nodekeymap_add_neq; [ exact (IH Hnd' Hoct r occ e Hin Hv) |].
      intro Hkeq. apply Hni. apply in_map_iff. exists (r, occ). split; [ cbn [fst]; congruence | exact Hin ].
    + exact (IH Hnd' Hoct r occ e Hin Hv).
Qed.

(* ---- OPERAND-CLOSURE of the visit stream (discharges [psm_fold_find]'s side condition): a conversion's
   operand is a LATER preorder node in the SAME file, so it lies in the ALREADY-FOLDED tail [l2]. ---- *)

Lemma SS_prefix_lt {A} (R : A -> A -> Prop) (a : list A) (v : A) (b : list A) :
  StronglySorted R (a ++ v :: b) -> Forall (fun z => R z v) a.
Proof.
  induction a as [|y a IH]; intro Hss; [constructor|].
  cbn [app] in Hss. apply StronglySorted_inv in Hss. destruct Hss as [Hss Hall].
  constructor; [ rewrite Forall_forall in Hall; apply Hall, in_or_app; right; left; reflexivity | apply IH; exact Hss ].
Qed.

Lemma ss_after_local {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) P y S :
  StronglySorted Pos.lt (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) l) ->
  l = P ++ y :: S ->
  forall z, In z l -> (GoIndex.Snap.node_ref_local (fst y) < GoIndex.Snap.node_ref_local (fst z))%positive -> In z S.
Proof.
  intros Hss Hsplit z Hz Hlt. subst l. rewrite map_app in Hss. cbn [map] in Hss.
  pose proof (SS_prefix_lt _ (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) P)
                (GoIndex.Snap.node_ref_local (fst y))
                (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) S) Hss) as Hpre.
  apply in_app_or in Hz. destruct Hz as [HzP | [Hzy | HzS]].
  - exfalso. rewrite Forall_forall in Hpre.
    assert (Hzin : In (GoIndex.Snap.node_ref_local (fst z)) (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) P))
      by (apply in_map_iff; exists z; split; [reflexivity | exact HzP]).
    exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hlt (Hpre _ Hzin))).
  - subst z. exact (False_ind _ (Pos.lt_irrefl _ Hlt)).
  - exact HzS.
Qed.

Lemma split_unique {A} (x : A) (l1 l2 a b : list A) :
  l1 ++ x :: l2 = a ++ x :: b -> ~ In x l1 -> ~ In x a -> l2 = b.
Proof.
  revert a; induction l1 as [|y l1 IH]; intros a Heq Hnl1 Hna.
  - destruct a as [|z a]; cbn [app] in Heq.
    + injection Heq as Hrest. exact Hrest.
    + injection Heq as He Hrest. exfalso. apply Hna. left. symmetry; exact He.
  - destruct a as [|z a]; cbn [app] in Heq.
    + injection Heq as He Hrest. exfalso. apply Hnl1. left. exact He.
    + injection Heq as He Hrest. apply (IH a Hrest);
        [ intro Hbad; apply Hnl1; right; exact Hbad | intro Hbad; apply Hna; right; exact Hbad ].
Qed.

Lemma prog_visit_not_in_prefix {p} (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) l1 r occ l2 :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) L) -> L = l1 ++ (r, occ) :: l2 -> ~ In (r, occ) l1.
Proof.
  intros Hnd HL Hbad. rewrite HL, map_app in Hnd. cbn [map fst] in Hnd.
  apply NoDup_remove_2 in Hnd. apply Hnd, in_or_app. left.
  apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hbad].
Qed.

Lemma prog_visit_operand_closed (p : GoProgram) :
  forall l1 r occ l2, prog_visit p = l1 ++ (r, occ) :: l2 ->
    forall e x, GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
    exists r' occ', GoIndex.Snap.node_ref_key r' = operand_key r /\ GoIndex.view_expr occ' = Some x /\ In (r', occ') l2.
Proof.
  intros l1 r occ l2 Hsplit e x Hv Hc.
  assert (Hin_ro : In (r, occ) (prog_visit p)) by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  destruct (prog_visit_operand p r occ e x Hin_ro Hv Hc) as [r' [Hin'p [Hkey Hvx]]].
  exists r', (GoIndex.Snap.source_occurrence_of_ref r'). split; [exact Hkey | split; [exact Hvx |]].
  pose proof Hin_ro as Hb0. rewrite prog_visit_flat_map in Hb0. apply in_flat_map in Hb0. destruct Hb0 as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [_ Hfile].
  pose proof (GoIndex.Snap.node_ref_key_eq r') as Hk'. rewrite Hkey in Hk'. unfold operand_key in Hk'.
  rewrite GoIndex.Snap.node_ref_key_eq in Hk'. cbn [GoIndex.nk_file] in Hk'. rewrite Hfile in Hk'.
  injection Hk' as Hpatheq Hloceq.
  assert (Hfile' : GoIndex.Snap.node_ref_file r' = fr) by (apply GoIndex.Snap.file_ref_path_inj; symmetry; exact Hpatheq).
  pose proof (GoIndex.Snap.visit_file_complete p fr r' Hfile') as Hin'block.
  apply in_split in Hrb. destruct Hrb as [P [S Hvfsplit]].
  assert (Hin'S : In (r', GoIndex.Snap.source_occurrence_of_ref r') S).
  { apply (ss_after_local (GoIndex.Snap.visit_file fr) P (r, occ) S (GoIndex.Snap.visit_file_order p fr) Hvfsplit
             (r', GoIndex.Snap.source_occurrence_of_ref r') Hin'block).
    cbn [fst]. rewrite <- Hloceq. apply Pos.lt_succ_diag_r. }
  apply in_split in Hb. destruct Hb as [B1 [B2 Hbsplit]].
  assert (Hbv : binding_visit p b = GoIndex.Snap.visit_file fr) by (unfold binding_visit; rewrite Ef; reflexivity).
  assert (Hpv : prog_visit p = (flat_map (binding_visit p) B1 ++ P) ++ (r, occ) :: (S ++ flat_map (binding_visit p) B2)).
  { rewrite prog_visit_flat_map, Hbsplit, flat_map_app. cbn [flat_map]. rewrite Hbv, Hvfsplit.
    rewrite <- !app_assoc. reflexivity. }
  pose proof (prog_visit_key_nodup p) as Hnd.
  assert (Hl2 : l2 = S ++ flat_map (binding_visit p) B2).
  { apply (split_unique (r, occ) l1 l2 (flat_map (binding_visit p) B1 ++ P) (S ++ flat_map (binding_visit p) B2)).
    - rewrite <- Hsplit. exact Hpv.
    - exact (prog_visit_not_in_prefix (prog_visit p) l1 r occ l2 Hnd Hsplit).
    - exact (prog_visit_not_in_prefix (prog_visit p) (flat_map (binding_visit p) B1 ++ P) r occ
               (S ++ flat_map (binding_visit p) B2) Hnd Hpv). }
  rewrite Hl2. apply in_or_app. left. exact Hin'S.
Qed.

(** STATUS-MAP EXACTNESS (from the ONE visit-stream fold): at each visited expression occurrence's key, the
    status map holds exactly that occurrence's [const_info] — read O(1), one [const_info_step] per occurrence,
    no separate source recursion. *)
Lemma prog_status_map_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_status_map p) = Some (const_info e).
Proof.
  intros Hin Hv. unfold prog_status_map.
  exact (psm_fold_find (prog_visit p) (prog_visit_key_nodup p) (prog_visit_operand_closed p) r occ e Hin Hv).
Qed.

(** STATUS-MAP OPERAND EXACTNESS: the operand key of a visited conversion holds the operand's exact [const_info]
    (the operand is itself a visited occurrence — [prog_visit_operand] — read at its own key = [operand_key]). *)
Lemma prog_status_map_find_operand (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
  GoIndex.NodeKeyMapBase.find (operand_key r) (prog_status_map p) = Some (const_info x).
Proof.
  intros Hin Hv Hc. destruct (prog_visit_operand p r occ e x Hin Hv Hc) as [r' [Hin' [Hkey Hvx]]].
  rewrite <- Hkey. exact (prog_status_map_find p r' (GoIndex.Snap.source_occurrence_of_ref r') x Hin' Hvx).
Qed.

(* ---- the SINGLE-PASS expression-fact map: fold the visit stream, keying each occurrence's fact by its
   NodeKey, taking its constant status from the precomputed [prog_status_map] (O(1), never a [const_info]
   rescan).  Its per-node fact is EXACTLY the specification [occ_expr_fact]. ---- *)

(* the use-context resolution DERIVED from an already-computed ConstInfo (no [const_info] / [resolve_expr_const]
   rescan): a println-argument root resolves its status, everything else has no use resolution. *)
Definition resolve_ci (ci : ConstInfo) : option ResolvedConst :=
  match resolve_const_info ci with
  | Some rc => if use_allowsb UsePrintlnArg (resolved_const_type rc) then Some rc else None
  | None => None
  end.
Definition occ_use_resolved_ci (o : GoIndex.SourceOccurrence) (ci : ConstInfo) : option ResolvedConst :=
  match GoIndex.occurrence_role o with GoIndex.RPrintlnArg _ => resolve_ci ci | _ => None end.

(* the status-map version reads the ConstInfo from [ci] (the occurrence's own status); [occ_use_resolved_ci]
   AGREES with the [occ_use_resolved] spec when [ci] is the occurrence's [const_info]. *)
Lemma occ_use_resolved_ci_eq : forall o e ci,
  GoIndex.view_expr o = Some e -> const_info e = Some ci -> occ_use_resolved_ci o ci = occ_use_resolved o.
Proof.
  intros o e ci Hv Hc. unfold occ_use_resolved_ci, occ_use_resolved, resolve_ci.
  destruct (GoIndex.occurrence_role o); try reflexivity.
  rewrite Hv. unfold resolve_expr_const. rewrite Hc. reflexivity.
Qed.

Definition add_occ_fact_sm {p} (smap : GoIndex.NodeKeyMapBase.t (option ConstInfo))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (m : GoIndex.NodeKeyMapBase.t ExprFact)
  : GoIndex.NodeKeyMapBase.t ExprFact :=
  match GoIndex.view_expr (snd ro) with
  | Some _ =>
      match GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (fst ro)) smap with
      | Some (Some ci) => GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (fst ro))
                                                     (mkExprFact ci (occ_use_resolved_ci (snd ro) ci)) m
      | _ => m
      end
  | None => m
  end.

Definition prog_expr_facts (p : GoProgram) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right (add_occ_fact_sm (prog_status_map p)) (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_visit p).

Lemma fold_ext_in {A B} (f g : A -> B -> B) (init : B) (l : list A) :
  (forall a b, In a l -> f a b = g a b) -> fold_right f init l = fold_right g init l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [fold_right]. rewrite IH by (intros a' b Ha'; apply H; right; exact Ha').
  apply H; left; reflexivity.
Qed.

(* on the visit stream, the single-pass step agrees with the [add_occ_fact] specification. *)
Lemma add_occ_fact_sm_eq (p : GoProgram) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) :
  In ro (prog_visit p) -> add_occ_fact_sm (prog_status_map p) ro m = add_occ_fact ro m.
Proof.
  intro Hin. destruct ro as [r occ]. unfold add_occ_fact_sm, add_occ_fact, occ_expr_fact. cbn [snd fst].
  destruct (GoIndex.view_expr occ) as [e|] eqn:Hv; [|reflexivity].
  rewrite (prog_status_map_find p r occ e Hin Hv).
  destruct (const_info e) as [ci|] eqn:Hc; [| reflexivity].
  rewrite (occ_use_resolved_ci_eq occ e ci Hv Hc). reflexivity.
Qed.

Lemma prog_expr_facts_eq_spec (p : GoProgram) :
  prog_expr_facts p = fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_visit p).
Proof.
  unfold prog_expr_facts. apply fold_ext_in. intros ro m Hin. apply add_occ_fact_sm_eq; exact Hin.
Qed.

(** PROGRAM-LEVEL FACT EXACTNESS: the fact at a program-visited ref's key is EXACTLY that occurrence's fact
    (the single-pass map agrees with the [occ_expr_fact] specification). *)
Lemma prog_expr_facts_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_expr_facts p) = occ_expr_fact occ.
Proof.
  intro Hin. rewrite prog_expr_facts_eq_spec. apply fold_facts_find; [ apply prog_visit_key_nodup | exact Hin ].
Qed.

(** DOMAIN EXACTNESS: EVERY key with an entry is a VISITED occurrence's key whose fact is exactly the stored
    one — so no non-expression / file-root / foreign key can carry a fact (a forged entry is unrepresentable). *)
Lemma fold_add_occ_fact_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) k f :
  GoIndex.NodeKeyMapBase.find k (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = Some f ->
  exists ro, In ro l /\ GoIndex.Snap.node_ref_key (fst ro) = k /\ occ_expr_fact (snd ro) = Some f.
Proof.
  induction l as [|ro rest IH]; intro Hf.
  - rewrite GoIndex.NodeKeyMapFacts.empty_o in Hf; discriminate Hf.
  - cbn [fold_right] in Hf. unfold add_occ_fact in Hf.
    destruct (occ_expr_fact (snd ro)) as [f0|] eqn:Ef.
    + destruct (GoIndex.thm8_nodekey_eq_dec (GoIndex.Snap.node_ref_key (fst ro)) k) as [He|Hne].
      * subst k. rewrite GoIndex.nodekeymap_add_eq in Hf. injection Hf as <-.
        exists ro. split; [left; reflexivity | split; [reflexivity | exact Ef]].
      * rewrite GoIndex.nodekeymap_add_neq in Hf by exact Hne.
        destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
    + destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Lemma prog_expr_facts_domain (p : GoProgram) k f :
  GoIndex.NodeKeyMapBase.find k (prog_expr_facts p) = Some f ->
  exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r = k /\ occ_expr_fact occ = Some f.
Proof.
  rewrite prog_expr_facts_eq_spec. intro Hf.
  destruct (fold_add_occ_fact_domain (prog_visit p) k f Hf) as [[r occ] [Hin [Hk Hfe]]].
  exists r, occ. cbn [fst snd] in *. split; [exact Hin | split; [exact Hk | exact Hfe]].
Qed.

(** §10/§27 — the SEALED expression-fact table: the standard NodeKey map + its two exactness proofs (domain =
    exactly the visited expression occurrences with a fact; each visited occurrence's fact is exact).  A forged
    table with a foreign/file-root key is unrepresentable; the fact of any expression reference is recoverable. *)
Record ExprFactTable (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type := mkExprFactTable {
  eft_map      : GoIndex.NodeKeyMapBase.t ExprFact ;
  eft_domain   : forall k f, GoIndex.NodeKeyMapBase.find k eft_map = Some f ->
                   exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
                     /\ GoIndex.Snap.node_ref_key r = k /\ occ_expr_fact occ = Some f ;
  eft_complete : forall r occ, In (r, occ) (prog_visit p) ->
                   GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) eft_map = occ_expr_fact occ
}.
Arguments mkExprFactTable {p ip} _ _ _.
Arguments eft_map {p ip} _.
Arguments eft_domain {p ip} _.
Arguments eft_complete {p ip} _.

Definition prog_expr_fact_table (p : GoProgram) (ip : GoIndex.IndexedProgram p) : ExprFactTable p ip :=
  mkExprFactTable (prog_expr_facts p) (prog_expr_facts_domain p) (prog_expr_facts_find p).

(* ---- the EXPRESSION DECISION: every println argument resolves IFF the program is [ProgramTyped] ---- *)

Lemma forallb_flat_map {A B} (f : B -> bool) (g : A -> list B) (l : list A) :
  forallb f (flat_map g l) = forallb (fun x => forallb f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite forallb_app, IH; reflexivity]. Qed.

(* =============================================================================================================
   §20 (moved from GoTypes) — THE PER-OCCURRENCE TYPING PREDICATE.  GoCompile is the SOLE meeting point of
   GoIndex identity and GoTypes semantics, so this occurrence/traversal bridge (which needs BOTH [SourceOccurrence]
   / [occs_file] from GoIndex and [expr_typedb] / [source_file_typedb] from GoTypes) lives HERE — GoTypes owns
   the type/constant relation only and imports no GoIndex.  [occ_arg_typedb] is the leaf typing decision over ONE
   source occurrence: a println-argument occurrence is typed iff its expression resolves (through the SAME
   [GoTypes.expr_typedb] resolver — no semantic judgment duplicated); every other occurrence is vacuously typed.
   [occs_file_typedb_eq] proves that folding it over the canonical occurrence stream ([occs_file]) equals the
   existing [source_file_typedb].  [analyze] CONSUMES this over its retained visit stream.
   ============================================================================================================= *)

(* the per-occurrence typing decision on the ORIGINAL syntax the traversal delivers: only a println-argument
   expression occurrence carries a semantic obligation (delegated to [expr_typedb UsePrintlnArg]); every other
   occurrence (file root, package clause, declaration, statement, conversion operand) is vacuously typed. *)
Definition occ_arg_typedb (o : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.occurrence_role o with
  | GoIndex.RPrintlnArg _ => match GoIndex.view_expr o with Some e => GoTypes.expr_typedb GoTypes.UsePrintlnArg e | None => true end
  | _ => true
  end.

Lemma occ_arg_typedb_operand : forall e par sub,
  occ_arg_typedb (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) GoIndex.RConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occ_arg_typedb_printlnarg : forall e par aidx sub,
  occ_arg_typedb (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) (GoIndex.RPrintlnArg aidx) sub)
  = GoTypes.expr_typedb GoTypes.UsePrintlnArg e.
Proof. reflexivity. Qed.

(* every occurrence inside a conversion operand carries role [RConversionOperand], hence is vacuously typed. *)
Lemma occs_expr_operand_true : forall e parent me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = true.
Proof.
  induction e as [ b | n | n | s | it x IHx | df | ft x IHx | dc | ct x IHx ];
    intros parent me; cbn [GoIndex.occs_expr forallb snd]; rewrite occ_arg_typedb_operand.
  1,2,3,4,6,8: reflexivity.
  all: rewrite Bool.andb_true_l; apply IHx.
Qed.

(* one println argument's occurrence stream types exactly as the existing [expr_typedb UsePrintlnArg]. *)
Lemma occs_arg_typedb_eq : forall e parent aidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_arg parent aidx me e) = GoTypes.expr_typedb GoTypes.UsePrintlnArg e.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b | n | n | s | it x | df | ft x | dc | ct x ];
    cbn [GoIndex.occs_expr forallb snd]; rewrite occ_arg_typedb_printlnarg.
  1,2,3,4,6,8: apply Bool.andb_true_r.
  all: rewrite occs_expr_operand_true; apply Bool.andb_true_r.
Qed.

Lemma occs_args_typedb_eq : forall es parent aidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_args parent aidx me es)
  = forallb (GoTypes.expr_typedb GoTypes.UsePrintlnArg) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me.
  - reflexivity.
  - cbn [GoIndex.occs_args]. rewrite forallb_app, occs_arg_typedb_eq, IH. reflexivity.
Qed.

Lemma occs_stmt_typedb_eq : forall s parent sidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_stmt parent sidx me s) = GoTypes.stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [GoIndex.occs_stmt forallb snd occ_arg_typedb GoIndex.occurrence_role].
  rewrite occs_args_typedb_eq. reflexivity.
Qed.

Lemma occs_stmts_typedb_eq : forall ss parent sidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_stmts parent sidx me ss) = forallb GoTypes.stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me.
  - reflexivity.
  - cbn [GoIndex.occs_stmts]. rewrite forallb_app, occs_stmt_typedb_eq, IH. reflexivity.
Qed.

Lemma occs_decl_typedb_eq : forall d parent didx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_decl parent didx me d) = GoTypes.decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [GoIndex.occs_decl forallb snd occ_arg_typedb GoIndex.occurrence_role].
  rewrite occs_stmts_typedb_eq. reflexivity.
Qed.

Lemma occs_decls_typedb_eq : forall ds parent didx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_decls parent didx me ds) = forallb GoTypes.decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me.
  - reflexivity.
  - cbn [GoIndex.occs_decls]. rewrite forallb_app, occs_decl_typedb_eq, IH. reflexivity.
Qed.

(* the WHOLE file's occurrence stream types exactly as the existing [source_file_typedb] (the file-root and
   package-clause occurrences are vacuously typed; the body delegates to [occs_decls_typedb_eq]). *)
Lemma occs_file_typedb_eq : forall f,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_file f) = source_file_typedb f.
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl] eqn:E.
  - cbn [forallb snd occ_arg_typedb GoIndex.occurrence_role].
    rewrite occs_decls_typedb_eq. unfold source_file_typedb, file_typedb. reflexivity.
  - destruct i.
Qed.

(** one file's argument occurrences resolve iff the file types (the §19 traversal projects [occs_file], reusing
    the [occ_arg_typedb] = [source_file_typedb] bridge). *)
Lemma visit_file_arg_typedb {p} (fr : GoIndex.Snap.FileRef p) :
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.Snap.visit_file fr)
  = source_file_typedb (GoIndex.Snap.file_ref_source fr).
Proof.
  rewrite GoTypes.forallb_map_snd, GoIndex.Snap.visit_file_snd, <- GoTypes.forallb_map_snd.
  apply occs_file_typedb_eq.
Qed.

(** the per-occurrence "argument resolves" check folded over the whole program. *)
Definition expr_all_ok (p : GoProgram) : bool :=
  forallb (fun x => occ_arg_typedb (snd x)) (prog_visit p).

(** DECISION EXACTNESS: [expr_all_ok] is EXACTLY [program_typedb] (hence [ProgramTyped]).  This is the
    expression half of [AnalysisOK <-> GoCompile]: no expression diagnostic <-> every argument resolves. *)
Lemma expr_all_ok_program_typedb (p : GoProgram) : expr_all_ok p = program_typedb p.
Proof.
  unfold expr_all_ok. rewrite prog_visit_flat_map, forallb_flat_map. unfold program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_arg_typedb, Hsrc. reflexivity.
Qed.

Lemma expr_all_ok_ProgramTyped (p : GoProgram) : expr_all_ok p = true <-> GoTypes.ProgramTyped p.
Proof. rewrite expr_all_ok_program_typedb. apply GoTypes.program_typedb_iff. Qed.

(* ---- the PACKAGE DECISION: every package has exactly one main IFF [AllPackagesOneMain] ---- *)

(** the per-package "exactly one main" check over the canonical package enumeration. *)
Definition pkg_all_ok (p : GoProgram) : bool :=
  forallb (fun b => Nat.eqb (ps_main_count (snd b)) 1) (PM.elements (package_summaries (prog_files p))).

Lemma pkg_all_ok_AllPackagesOneMain (p : GoProgram) : pkg_all_ok p = true <-> AllPackagesOneMain p.
Proof.
  unfold pkg_all_ok, AllPackagesOneMain.
  rewrite (forallb_Forall (fun b => Nat.eqb (ps_main_count (snd b)) 1%nat) (fun b => ps_main_count (snd b) = 1%nat)
             (PM.elements (package_summaries (prog_files p))) (fun b => Nat.eqb_eq (ps_main_count (snd b)) 1%nat)).
  split.
  - intros Hf dir s Hmt.
    apply PMF.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros Hall. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PMF.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

(* ---- the COMBINED analysis DECISION: an analysis-native boolean (NOT [prog_ok]) proved EXACTLY [GoCompile] ---- *)

Definition analysis_ok_b (p : GoProgram) : bool := expr_all_ok p && pkg_all_ok p.

Lemma analysis_ok_b_prog_ok (p : GoProgram) : analysis_ok_b p = prog_ok p.
Proof. unfold analysis_ok_b, prog_ok. rewrite expr_all_ok_program_typedb. reflexivity. Qed.

(* [GoCompile p] is defined below as exactly [ProgValid p]; the analysis decision equals it. *)
Lemma analysis_ok_b_ProgValid (p : GoProgram) : analysis_ok_b p = true <-> ProgValid p.
Proof. rewrite analysis_ok_b_prog_ok. apply prog_ok_iff. Qed.

Lemma analysis_ok_b_split (p : GoProgram) :
  analysis_ok_b p = true <-> expr_all_ok p = true /\ pkg_all_ok p = true.
Proof. unfold analysis_ok_b. rewrite Bool.andb_true_iff. reflexivity. Qed.

(* ============================================================================================================
   §8/§9 (C3) — the EXPRESSION diagnostic construction, per occurrence, with §9-SOUND anchors.

   The key move (no descent, no ref minting): the primary is the OCCURRENCE'S OWN reference.
   - a LOCALLY-failing conversion (its operand's [const_info] succeeds but its own [convert_const] fails) IS the
     innermost failing conversion — anchor [DRInvalidConversion] at its own ExprRef;
   - a println-argument occurrence whose [const_info] is an UNTYPED constant that does not default — anchor
     [DRDefaultNotRepresentable] at its own ExprRef.
   ([outer_context] is [] here — sound (vacuously) for §9; FINAL enriches it with the enclosing conversions.)
   ============================================================================================================ *)

Definition default_target_of (c : GoConst) : GoType :=
  match c with
  | CBool _    => TBool
  | CInt _     => TInteger IInt
  | CFloat _   => TFloat F64
  | CComplex _ => TComplex C128
  | CString _  => TString
  end.

(** a conversion whose operand succeeds but whose own conversion step fails — returns (target, operand status). *)
Definition local_conv_failure (e : GoExpr) : option (GoType * ConstInfo) :=
  match e with
  | EIntConvert t x =>
      match const_info x with
      | Some ci => match convert_const (TInteger t) ci with None => Some (TInteger t, ci) | Some _ => None end
      | None => None end
  | EFloatConvert t x =>
      match const_info x with
      | Some ci => match convert_const (TFloat t) ci with None => Some (TFloat t, ci) | Some _ => None end
      | None => None end
  | EComplexConvert t x =>
      match const_info x with
      | Some ci => match convert_const (TComplex t) ci with None => Some (TComplex t, ci) | Some _ => None end
      | None => None end
  | _ => None
  end.

(** the explicit-conversion SYNTAX projection: an expression is a conversion to type [t] of operand [x]. *)
Definition conv_targets (e : GoExpr) : option (GoType * GoExpr) :=
  match e with
  | EIntConvert t x     => Some (TInteger t, x)
  | EFloatConvert t x   => Some (TFloat t, x)
  | EComplexConvert t x => Some (TComplex t, x)
  | _                   => None
  end.

(** §9 (C3 FINAL) — a local conversion failure denotes EXACTLY: the expression is the explicit conversion to
    the reported target [t] of some operand [x] ([conv_targets]), [x]'s exact successful status is the reported
    [ci] ([const_info x = Some ci]), and the shared [convert_const] rejects it.  So the DRInvalidConversion
    primary/target/operand-status faithfully denote the reported explicit conversion. *)
Lemma local_conv_failure_char (e : GoExpr) (t : GoType) (ci : ConstInfo) :
  local_conv_failure e = Some (t, ci) ->
  exists x, conv_targets e = Some (t, x) /\ const_info x = Some ci /\ convert_const t ci = None.
Proof.
  intro H. destruct e as [ b|n1|n2|s| it x | df | ft x | dcx | ct x ]; try discriminate H; cbn [local_conv_failure] in H;
    (destruct (const_info x) as [ci'|] eqn:Ex; [| discriminate H];
     destruct (convert_const _ ci') as [c'|] eqn:Ec; [ discriminate H | injection H as Ht Hc; subst ];
     exists x; cbn [conv_targets]; rewrite Ex; split; [reflexivity | split; [reflexivity | exact Ec]]).
Qed.

(** a println-argument occurrence whose exact untyped constant does not default — returns (constant, default). *)
Definition arg_default_failure (occ : GoIndex.SourceOccurrence) (e : GoExpr) : option (GoConst * GoType) :=
  match GoIndex.occurrence_role occ with
  | GoIndex.RPrintlnArg _ =>
      match const_info e with
      | Some (CIUntyped c) => match default_const c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None
      end
  | _ => None
  end.

(** §14/§15 (C3 FINAL) — the explicit-conversion SYNTAX test on a DELIVERED occurrence (consumed by the
    one-pass [annotate_encl]): a node is a conversion iff its occurrence's OWN syntax is one of the three
    explicit conversions.  Reads only the delivered [SourceOccurrence] — no [node_at] recovery, no
    [visit_file] re-traversal — so it is snapshot-independent (source-determined). *)
Definition is_conversion_occ (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some (EIntConvert _ _) | Some (EFloatConvert _ _) | Some (EComplexConvert _ _) => true
  | _ => false
  end.

(** §14/§15 (C3 FINAL) — the ONE-PASS enclosing-conversion context.  A single FORWARD pass over the RETAINED
    preorder file stream carries the open-conversion stack (nearest-first, push-front); each occurrence is
    annotated with its enclosing-conversion refs = [map fst] of the currently-open stack (its strict
    conversion ancestors).  Entries whose subtree has closed ([node_subtree_end < node_ref_local]) are popped;
    a conversion occurrence pushes its own [ExprRef] + subtree end AFTER recording.  No per-diagnostic
    [visit_file] re-traversal and no [node_at] recovery — only retained refs, index subtree metadata, and the
    delivered occurrence's own syntax ([is_conversion_occ]).  This IS the enclosing-context authority (the
    [outer_context] delivered to the diagnostic emitters); its erased form is a source function of the keyed
    stream ([annotate_encl_erased]), the basis for cross-snapshot report determinism. *)
Fixpoint annotate_encl {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (stack : list (GoIndex.ExprRef p * positive))
    (stream : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    : list ((GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p)) :=
  match stream with
  | [] => []
  | ro :: rest =>
      let open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro)) (snd e)) stack in
      let stack' := match GoIndex.as_expr idx (fst ro) with
                    | Some er => if is_conversion_occ (snd ro)
                                 then (er, GoIndex.Snap.node_subtree_end idx (fst ro)) :: open
                                 else open
                    | None => open
                    end in
      (ro, map fst open) :: annotate_encl idx stack' rest
  end.

Lemma flat_map_map {A B C} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [map flat_map]. rewrite IH. reflexivity. Qed.

(** the annotation preserves the underlying occurrence stream (it only attaches context). *)
Lemma annotate_encl_fst {p} (idx : GoIndex.Snap.SyntaxIndex p) stack stream :
  map fst (annotate_encl idx stack stream) = stream.
Proof.
  revert stack; induction stream as [|ro rest IH]; intro stack; [reflexivity|].
  cbn [annotate_encl map]. rewrite IH. reflexivity.
Qed.

(* §9 (C3 FINAL) — the annotation-STACK invariant: every open entry [(er, se)] is a genuine CONVERSION
   [ExprRef] (erasing to a node whose occurrence's syntax is a conversion) whose subtree end is [se]. *)
Definition estack_ok {p} (idx : GoIndex.Snap.SyntaxIndex p) (stack : list (GoIndex.ExprRef p * positive)) : Prop :=
  forall er se, In (er, se) stack ->
    GoIndex.as_expr idx (GoIndex.erase_ref er) = Some er
    /\ is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
    /\ GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er) = se.

(* filtering preserves the stack invariant. *)
Lemma estack_ok_filter {p} (idx : GoIndex.Snap.SyntaxIndex p) P stack :
  estack_ok idx stack -> estack_ok idx (filter P stack).
Proof. intros H er se Hin. apply filter_In in Hin. exact (H er se (proj1 Hin)). Qed.

(** §9 — the NESTED SCAR soundness: every enclosing-conversion ref delivered to occurrence [ro] is a genuine
    CONVERSION whose subtree STRICTLY contains [ro] (a strict-ancestor conversion — [node_ref_local < ro <=
    node_subtree_end]).  Requires the stream sorted by local (preorder) with the stack's entries all below the
    stream's locals — exactly the per-file [visit_file] block. *)
Lemma annotate_encl_ctx_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall stream stack,
  StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  estack_ok idx stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
  forall er, In er ctx ->
    is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
    /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))
    /\ Pos.le (GoIndex.Snap.node_ref_local (fst ro)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er)).
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hstk Hbnd roc ctx Hin er Her; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro0)) (snd e)) stack) in *.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
  destruct Hin as [Heq | Hin].
  - injection Heq as Hro Hctx. subst roc ctx.
    apply in_map_iff in Her. destruct Her as [[er2 se] [Her2 Hin2]]. cbn [fst] in Her2. subst er2.
    pose proof Hin2 as Hin2'. apply filter_In in Hin2'. destruct Hin2' as [Hstack Hle]. apply Pos.leb_le in Hle.
    destruct (Hstk er se Hstack) as [_ [Hconv Hse]].
    split; [ exact Hconv | split ].
    + exact (Hbnd ro0 er se (or_introl eq_refl) Hstack).
    + rewrite Hse. exact Hle.
  - refine (IH _ Hsort0 (fun ro' Hr => Hval ro' (or_intror Hr)) _ _ roc ctx Hin er Her).
    + (* estack_ok idx stack' *)
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- intros e s [Hh | Ht].
           ++ injection Hh as He Hs. subst e s.
              rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
              split; [exact Ea | split; [ rewrite <- (Hval ro0 (or_introl eq_refl)); exact Hc0 | reflexivity ]].
           ++ exact (estack_ok_filter idx _ stack Hstk e s Ht).
        -- exact (estack_ok_filter idx _ stack Hstk).
      * exact (estack_ok_filter idx _ stack Hstk).
    + (* the bound for rest: stack' entries below rest's locals *)
      intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (GoIndex.Snap.node_ref_local (fst ro0)) (GoIndex.Snap.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- destruct Hes as [Hh | Ht].
           ++ injection Hh as He Hs. subst e.
              rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea). exact Hlt0.
           ++ pose proof Ht as Ht'. apply filter_In in Ht'.
              exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
        -- pose proof Hes as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma StronglySorted_filter {A} (R : A -> A -> Prop) (P : A -> bool) l :
  StronglySorted R l -> StronglySorted R (filter P l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd]. cbn [filter].
  destruct (P a); [| apply IH; exact Hs].
  constructor; [apply IH; exact Hs|]. rewrite Forall_forall in Hhd |- *.
  intros x Hx. apply filter_In in Hx. apply Hhd. exact (proj1 Hx).
Qed.

Lemma StronglySorted_map {A B} (R : B -> B -> Prop) (f : A -> B) l :
  StronglySorted (fun x y => R (f x) (f y)) l -> StronglySorted R (map f l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map]. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [x [Hxy Hx]]. subst y. exact (Hhd x Hx).
Qed.

Lemma StronglySorted_NoDup {A} (R : A -> A -> Prop) l :
  (forall a, ~ R a a) -> StronglySorted R l -> NoDup l.
Proof.
  intro Hirr. induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [| apply IH; exact Hs].
  intro Hina. rewrite Forall_forall in Hhd. exact (Hirr a (Hhd a Hina)).
Qed.

Lemma StronglySorted_impl_in {A} (R R' : A -> A -> Prop) l :
  (forall x y, In x l -> In y l -> R x y -> R' x y) -> StronglySorted R l -> StronglySorted R' l.
Proof.
  intros Himp H. induction l as [|a l IH]; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor.
  - apply IH; [| exact Hs]. intros x y Hx Hy. apply Himp; right; assumption.
  - rewrite Forall_forall in Hhd |- *. intros x Hx. apply Himp; [left; reflexivity | right; exact Hx | exact (Hhd x Hx)].
Qed.

Lemma StronglySorted_app {A} (R : A -> A -> Prop) l1 l2 :
  StronglySorted R l1 -> StronglySorted R l2 -> (forall a b, In a l1 -> In b l2 -> R a b) ->
  StronglySorted R (l1 ++ l2).
Proof.
  intros H1 H2 Hcross. induction l1 as [|a l1 IH]; [exact H2|].
  apply StronglySorted_inv in H1. destruct H1 as [Hs Hhd]. cbn [app]. constructor.
  - apply IH; [exact Hs | intros b c Hb Hc; apply Hcross; [right; exact Hb | exact Hc]].
  - rewrite Forall_forall. intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx | Hx].
    + rewrite Forall_forall in Hhd. exact (Hhd x Hx).
    + apply Hcross; [left; reflexivity | exact Hx].
Qed.

(* the annotation-STACK is same-file and STRICTLY DESCENDING by local (front = last pushed = deepest =
   NEAREST); its projection to the [ExprRef] context is thus same-file, nearest-first, and duplicate-free. *)
Definition estack_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p)
    (stack : list (GoIndex.ExprRef p * positive)) : Prop :=
  Forall (fun e => GoIndex.Snap.node_ref_file (GoIndex.erase_ref (fst e)) = fr) stack
  /\ StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref (fst y)))
                                       (GoIndex.Snap.node_ref_local (GoIndex.erase_ref (fst x)))) stack.

Lemma estack_wf_filter {p} (idx : GoIndex.Snap.SyntaxIndex p) fr P stack :
  estack_wf idx fr stack -> estack_wf idx fr (filter P stack).
Proof.
  intros [Hf Hs]. split.
  - apply Forall_forall. intros e He. apply filter_In in He. rewrite Forall_forall in Hf. exact (Hf e (proj1 He)).
  - apply StronglySorted_filter; assumption.
Qed.

(** §9 (C3 FINAL) — the nested scar is SAME-FILE, NEAREST-FIRST, and DUPLICATE-FREE: over a per-file
    [visit_file] block the delivered [outer_context] is all in that file, and strictly descending by local
    (deepest/nearest enclosing conversion first) — whence [NoDup]. *)
Lemma annotate_encl_ctx_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  forall stream stack,
  StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro) /\ GoIndex.Snap.node_ref_file (fst ro) = fr) ->
  estack_wf idx fr stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
    Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = fr) ctx
    /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx.
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hwf Hbnd roc ctx Hin; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro0)) (snd e)) stack) in *.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
  assert (Hwfopen : estack_wf idx fr open) by (apply estack_wf_filter; exact Hwf).
  destruct Hin as [Heq | Hin].
  - injection Heq as Hro Hctx. subst roc ctx. destruct Hwfopen as [Hf Hs].
    split.
    + rewrite Forall_forall. intros er Herin. apply in_map_iff in Herin.
      destruct Herin as [[e s] [Hes Hin']]. cbn [fst] in Hes. subst er.
      rewrite Forall_forall in Hf. exact (Hf (e, s) Hin').
    + apply (StronglySorted_map (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b))
                                                   (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a)))
              fst open). exact Hs.
  - refine (IH _ Hsort0 (fun ro' Hr => Hval ro' (or_intror Hr)) _ _ roc ctx Hin).
    + destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ]; try (exact Hwfopen).
      destruct Hwfopen as [Hf Hs]. split.
      * constructor; [| exact Hf]. cbn [fst].
        rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
        exact (proj2 (Hval ro0 (or_introl eq_refl))).
      * constructor; [exact Hs|]. apply Forall_forall. intros [e s] He. cbn [fst].
        rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
        pose proof He as He'. apply filter_In in He'.
        exact (Hbnd ro0 e s (or_introl eq_refl) (proj1 He')).
    + intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (GoIndex.Snap.node_ref_local (fst ro0)) (GoIndex.Snap.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ].
      * destruct Hes as [Hh | Ht].
        -- injection Hh as He Hs. subst e.
           rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea). exact Hlt0.
        -- pose proof Ht as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma StronglySorted_map_inv {A B} (R : B -> B -> Prop) (f : A -> B) (l : list A) :
  StronglySorted R (map f l) -> StronglySorted (fun x y => R (f x) (f y)) l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map] in H. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros x Hx. apply Hhd. exact (in_map f l x Hx).
Qed.

Definition annotate_program {p} (idx : GoIndex.Snap.SyntaxIndex p)
  : list ((GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p)) :=
  flat_map (annotate_encl idx []) (prog_blocks p).

(** §9 — lift the nested-scar soundness to the whole program: every enclosing-conversion ref delivered to any
    annotated occurrence is a strict-ancestor conversion (its subtree strictly contains the occurrence). *)
Lemma annotate_program_ctx_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall ro ctx er,
  In (ro, ctx) (annotate_program idx) -> In er ctx ->
  is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
  /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))
  /\ Pos.le (GoIndex.Snap.node_ref_local (fst ro)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er)).
Proof.
  intros ro ctx er Hin Her. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold prog_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  refine (annotate_encl_ctx_sound idx (GoIndex.Snap.visit_file fr) [] _ _ _ _ ro ctx Hin er Her).
  - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
  - intros [r occ] Hro. destruct (GoIndex.Snap.visit_file_view p fr r occ Hro) as [Ho _]. exact Ho.
  - intros er0 se [].
  - intros ro0 er0 se _ [].
Qed.

(** §9 — the whole-program nested scar is SAME-FILE (as the primary), NEAREST-FIRST, and DUPLICATE-FREE. *)
Lemma annotate_program_ctx_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall ro ctx,
  In (ro, ctx) (annotate_program idx) ->
  Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = GoIndex.Snap.node_ref_file (fst ro)) ctx
  /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx
  /\ NoDup ctx.
Proof.
  intros ro ctx Hin. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold prog_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  assert (Hroin : In ro (GoIndex.Snap.visit_file fr))
    by (rewrite <- (annotate_encl_fst idx [] (GoIndex.Snap.visit_file fr)); exact (in_map fst _ _ Hin)).
  assert (Hrf : GoIndex.Snap.node_ref_file (fst ro) = fr).
  { destruct ro as [r occ]. destruct (GoIndex.Snap.visit_file_view p fr r occ Hroin) as [_ Hf]. exact Hf. }
  assert (Hprops : Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = fr) ctx
                 /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b))
                                                      (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx).
  { refine (annotate_encl_ctx_wf idx fr (GoIndex.Snap.visit_file fr) [] _ _ _ _ ro ctx Hin).
    - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
    - intros [r occ] Hro. destruct (GoIndex.Snap.visit_file_view p fr r occ Hro) as [Ho Hf]. split; assumption.
    - split; constructor.
    - intros ro0 er0 se _ []. }
  destruct Hprops as [Hfile Hss].
  rewrite Hrf. split; [exact Hfile | split; [exact Hss |]].
  exact (StronglySorted_NoDup _ ctx (fun a => Pos.lt_irrefl _) Hss).
Qed.

Lemma annotate_program_fst {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map fst (annotate_program idx) = prog_visit p.
Proof.
  unfold annotate_program, prog_visit.
  induction (prog_blocks p) as [|b L IH]; [reflexivity|].
  cbn [flat_map concat]. rewrite map_app, annotate_encl_fst, IH. reflexivity.
Qed.

(** the diagnostic(s) an occurrence emits (a singleton or nothing), anchored at its OWN validated ExprRef.
    The [outer] enclosing-conversion context is DELIVERED by the one-pass [annotate_program] annotation (§14/§15),
    never recomputed here — so no [visit_file]/[node_at] per diagnostic. *)
Definition occ_expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : list (DiagnosticReason p) :=
  match GoIndex.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match GoIndex.view_expr (snd ro) with
      | None => []
      | Some e =>
          match local_conv_failure e with
          | Some (t, ci) => [ DRInvalidConversion er outer t ci ]
          | None =>
              match arg_default_failure (snd ro) e with
              | Some (c, dt) => [ DRDefaultNotRepresentable er c dt ]
              | None => []
              end
          end
      end
  end.

(** §9 (C3 FINAL) — code-specific EXPRESSION-diagnostic soundness.  A local conversion failure genuinely
    FAILS the shared [convert_const] for the reported target. *)
Lemma local_conv_failure_sound : forall e t ci,
  local_conv_failure e = Some (t, ci) -> convert_const t ci = None.
Proof.
  intros e t ci H. unfold local_conv_failure in H.
  destruct e as [b|n|n0|s| it x |df| ft x |dcx| ct x ]; try discriminate H;
    (destruct (const_info x) as [ci'|]; [| discriminate H];
     destruct (convert_const _ ci') eqn:Ec; [ discriminate H | injection H as <- <-; exact Ec ]).
Qed.

(** §9 (C3 FINAL) — a [DRInvalidConversion] diagnostic DENOTES its reported code end-to-end: the [outer_context]
    is EXACTLY the delivered enclosing context; the primary [er] is the occurrence's OWN [ExprRef]; the
    occurrence's syntax IS the explicit conversion to the reported target [t] of operand [x] ([conv_targets]);
    the reported operand status [ci] is [x]'s exact successful [const_info]; and the shared [convert_const]
    genuinely REJECTS it.  So target/operand-status/primary faithfully denote the reported conversion. *)
Lemma occ_expr_diags_conv_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) ro outer er outer' t ci :
  In (DRInvalidConversion er outer' t ci) (occ_expr_diags idx outer ro) ->
  outer' = outer
  /\ GoIndex.as_expr idx (fst ro) = Some er
  /\ convert_const t ci = None
  /\ exists e x, GoIndex.view_expr (snd ro) = Some e /\ conv_targets e = Some (t, x) /\ const_info x = Some ci.
Proof.
  intro Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er2|] eqn:Ea; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc.
  - destruct Hin as [Heq|[]]. injection Heq as He Ho Ht Hc. subst er2 t' ci'.
    destruct (local_conv_failure_char e t ci Elc) as [x [Hct [Hci Hcv]]].
    split; [ symmetry; exact Ho
           | split; [ reflexivity
                    | split; [ exact Hcv
                             | exists e, x; split; [reflexivity | split; [exact Hct | exact Hci]]]]].
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|];
      [ destruct Hin as [Heq|[]]; discriminate Heq | destruct Hin ].
Qed.

(** §9 (C3 FINAL) — a [DRDefaultNotRepresentable] diagnostic DENOTES its reported code end-to-end: the primary
    [er] is the occurrence's OWN [ExprRef]; the occurrence is genuinely a PRINTLN ARGUMENT ([RPrintlnArg]) —
    the only use context that can default-fail; its syntax's exact status is the reported untyped constant
    [CIUntyped c]; that [c] does NOT default ([default_const c = None]); and the reported default target is
    EXACTLY [c]'s Go default ([default_target_of] — integer->int, float->float64, complex->complex128). *)
Lemma occ_expr_diags_default_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) ro outer er c dt :
  In (DRDefaultNotRepresentable er c dt) (occ_expr_diags idx outer ro) ->
  GoIndex.as_expr idx (fst ro) = Some er
  /\ (exists aidx, GoIndex.occurrence_role (snd ro) = GoIndex.RPrintlnArg aidx)
  /\ (exists e, GoIndex.view_expr (snd ro) = Some e /\ const_info e = Some (CIUntyped c))
  /\ default_const c = None
  /\ dt = default_target_of c.
Proof.
  intro Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er'|] eqn:Ea; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc; [ destruct Hin as [Heq|[]]; discriminate Heq |].
  destruct (arg_default_failure (snd ro) e) as [[c' dt']|] eqn:Ead; [| destruct Hin].
  destruct Hin as [Heq|[]]. injection Heq as He Hc Hd. subst er' c' dt'.
  unfold arg_default_failure in Ead.
  destruct (GoIndex.occurrence_role (snd ro)) as [ | | ai | si | ain | ] eqn:Erole; try discriminate Ead.
  destruct (const_info e) as [cinf|] eqn:Eci; try discriminate Ead.
  destruct cinf as [cc | ct tc]; [| discriminate Ead].
  destruct (default_const cc) eqn:Edc; [ discriminate Ead | injection Ead as Hcc Hdtc ]. subst c dt.
  split; [ reflexivity
         | split; [ exists ain; reflexivity
                  | split; [ exists e; split; [reflexivity | exact Eci]
                           | split; [ exact Edc | reflexivity ]]]].
Qed.

(* ---- the SINGLE-PASS diagnostic step: reads each occurrence's own status and (for a conversion) its
   OPERAND's status from the precomputed [prog_status_map] — never recomputing [const_info].  Proved to agree
   with the [occ_expr_diags] specification on the visit stream. ---- *)


Definition local_conv_failure_sm {p} (smap : GoIndex.NodeKeyMapBase.t (option ConstInfo))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : option (GoType * ConstInfo) :=
  match GoIndex.view_expr (snd ro) with
  | Some (EIntConvert t _) =>
      match GoIndex.NodeKeyMapBase.find (operand_key (fst ro)) smap with
      | Some (Some ci) => match convert_const (TInteger t) ci with None => Some (TInteger t, ci) | Some _ => None end
      | _ => None end
  | Some (EFloatConvert t _) =>
      match GoIndex.NodeKeyMapBase.find (operand_key (fst ro)) smap with
      | Some (Some ci) => match convert_const (TFloat t) ci with None => Some (TFloat t, ci) | Some _ => None end
      | _ => None end
  | Some (EComplexConvert t _) =>
      match GoIndex.NodeKeyMapBase.find (operand_key (fst ro)) smap with
      | Some (Some ci) => match convert_const (TComplex t) ci with None => Some (TComplex t, ci) | Some _ => None end
      | _ => None end
  | _ => None
  end.

Definition arg_default_failure_sm {p} (smap : GoIndex.NodeKeyMapBase.t (option ConstInfo))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : option (GoConst * GoType) :=
  match GoIndex.occurrence_role (snd ro) with
  | GoIndex.RPrintlnArg _ =>
      match GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (fst ro)) smap with
      | Some (Some (CIUntyped c)) => match default_const c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None end
  | _ => None
  end.

Definition occ_expr_diags_sm {p} (smap : GoIndex.NodeKeyMapBase.t (option ConstInfo))
    (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  : list (DiagnosticReason p) :=
  match GoIndex.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match local_conv_failure_sm smap ro with
      | Some (t, ci) => [ DRInvalidConversion er outer t ci ]
      | None =>
          match arg_default_failure_sm smap ro with
          | Some (c, dt) => [ DRDefaultNotRepresentable er c dt ]
          | None => []
          end
      end
  end.

Lemma local_conv_failure_sm_eq {p} (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  local_conv_failure_sm (prog_status_map p) (r, occ) = local_conv_failure e.
Proof.
  intros Hin Hv. unfold local_conv_failure_sm, local_conv_failure; cbn [fst snd]; rewrite Hv.
  destruct e as [ b|n1|n2|s| it x|df|ft x|dcx|ct x ]; try reflexivity.
  - rewrite (prog_status_map_find_operand p r occ (EIntConvert it x) x Hin Hv eq_refl); destruct (const_info x); reflexivity.
  - rewrite (prog_status_map_find_operand p r occ (EFloatConvert ft x) x Hin Hv eq_refl); destruct (const_info x); reflexivity.
  - rewrite (prog_status_map_find_operand p r occ (EComplexConvert ct x) x Hin Hv eq_refl); destruct (const_info x); reflexivity.
Qed.

Lemma arg_default_failure_sm_eq {p} (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  arg_default_failure_sm (prog_status_map p) (r, occ) = arg_default_failure occ e.
Proof.
  intros Hin Hv. unfold arg_default_failure_sm, arg_default_failure; cbn [fst snd].
  destruct (GoIndex.occurrence_role occ); try reflexivity.
  rewrite (prog_status_map_find p r occ e Hin Hv). destruct (const_info e) as [[c|t tc]|]; reflexivity.
Qed.

Lemma occ_expr_diags_sm_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :
  In ro (prog_visit p) -> occ_expr_diags_sm (prog_status_map p) idx outer ro = occ_expr_diags idx outer ro.
Proof.
  intro Hin. destruct ro as [r occ]. unfold occ_expr_diags_sm, occ_expr_diags; cbn [fst snd].
  destruct (GoIndex.as_expr idx r) as [er|] eqn:Ea; [|reflexivity].
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
  { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
    destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [He|]; [exact He|discriminate Ea]. }
  assert (Hocc : occ = GoIndex.Snap.source_occurrence_of_ref r).
  { pose proof Hin as HinC. rewrite prog_visit_flat_map in HinC. apply in_flat_map in HinC. destruct HinC as [b [_ Hrb]].
    unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [|destruct Hrb].
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Ho _]. exact Ho. }
  assert (Hkind : GoIndex.occurrence_kind occ = GoIndex.KExpression).
  { rewrite Hocc, <- (GoIndex.Snap.node_kind_matches_source p idx r). exact Hk. }
  destruct (GoIndex.kind_view_expr occ Hkind) as [e Hv]. rewrite Hv.
  rewrite (local_conv_failure_sm_eq r occ e Hin Hv), (arg_default_failure_sm_eq r occ e Hin Hv). reflexivity.
Qed.

Lemma flat_map_ext_in {A B} (f g : A -> list B) (l : list A) :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [flat_map]. rewrite (H a (or_introl eq_refl)), IH by (intros a' Ha'; apply H; right; exact Ha'). reflexivity.
Qed.

(* the production expression diagnostics: the SINGLE-PASS status step over the ONE-PASS annotated stream —
   each occurrence's enclosing-conversion context [snd roc] is DELIVERED by [annotate_program], its status is
   read from [prog_status_map]; no per-diagnostic [visit_file]/[node_at]. *)
Definition expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  flat_map (fun roc => occ_expr_diags_sm (prog_status_map p) idx (snd roc) (fst roc)) (annotate_program idx).

Lemma expr_diags_eq_spec {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  expr_diags idx = flat_map (fun roc => occ_expr_diags idx (snd roc) (fst roc)) (annotate_program idx).
Proof.
  unfold expr_diags. apply flat_map_ext_in. intros roc Hin. apply occ_expr_diags_sm_eq.
  rewrite <- (annotate_program_fst idx). exact (in_map fst _ _ Hin).
Qed.

(** §9 (C3 FINAL) — THE NESTED SCAR: every [outer_context] ref of an invalid-conversion diagnostic in the
    whole expression report is a genuine CONVERSION whose subtree STRICTLY contains the primary — a real
    strict-ancestor conversion, never fabricated or copied syntax.  (Delivered by the ONE-PASS annotation,
    proved sound by [annotate_program_ctx_sound].) *)
Lemma expr_diags_conv_scar_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) er outer t ci :
  In (DRInvalidConversion er outer t ci) (expr_diags idx) ->
  forall a, In a outer ->
    is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref a)) = true
    /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er))
    /\ Pos.le (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref a)).
Proof.
  intros Hin a Ha. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occ_expr_diags_conv_sound idx (fst roc) (snd roc) er outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_sound idx (fst roc) (snd roc) a Hroc2 Ha) as [Hconv [Hlt Hle]].
  assert (Her : GoIndex.erase_ref er = fst (fst roc))
    by exact (GoIndex.erase_as_kind idx (fst (fst roc)) GoIndex.KExpression er Hae).
  rewrite Her. split; [exact Hconv | split; [exact Hlt | exact Hle]].
Qed.

(** §9 (C3 FINAL) — the nested scar is SAME-FILE (as the primary), NEAREST-FIRST (deepest enclosing
    conversion first), and DUPLICATE-FREE for every invalid-conversion diagnostic in the whole report. *)
Lemma expr_diags_conv_scar_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) er outer t ci :
  In (DRInvalidConversion er outer t ci) (expr_diags idx) ->
  Forall (fun a => GoIndex.Snap.node_ref_file (GoIndex.erase_ref a) = GoIndex.Snap.node_ref_file (GoIndex.erase_ref er)) outer
  /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) outer
  /\ NoDup outer.
Proof.
  intro Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occ_expr_diags_conv_sound idx (fst roc) (snd roc) er outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_wf idx (fst roc) (snd roc) Hroc2) as [Hfile [Hss Hnd]].
  assert (Her : GoIndex.erase_ref er = fst (fst roc))
    by exact (GoIndex.erase_as_kind idx (fst (fst roc)) GoIndex.KExpression er Hae).
  rewrite Her. split; [exact Hfile | split; [exact Hss | exact Hnd]].
Qed.

(* ---- COMPLETENESS: [expr_diags] is empty IFF every argument resolves (= [program_typedb]) ---- *)

(** the PURE (index-free) per-occurrence "emits nothing" predicate: no locally-failing conversion here, and no
    defaulting-argument failure here. *)
Definition occ_local_ok (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some e => match local_conv_failure e with Some _ => false | None => true end
  | None => true
  end.
Definition occ_default_ok (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some e => match arg_default_failure occ e with Some _ => false | None => true end
  | None => true
  end.
Definition occ_emits_none_pure (occ : GoIndex.SourceOccurrence) : bool :=
  occ_local_ok occ && occ_default_ok occ.

(** every use-context type is allowed for a println argument (the type universe is exactly the allowed set). *)
Lemma use_allowsb_println_true : forall t, use_allowsb UsePrintlnArg t = true.
Proof. intro t; destruct t; reflexivity. Qed.

(** KEY: no conversion in a subtree locally fails IFF the subtree's [const_info] succeeds. *)
Lemma conv_ok_fold : forall e parent role me,
  forallb (fun x => occ_local_ok (snd x)) (GoIndex.occs_expr parent role me e)
  = match const_info e with Some _ => true | None => false end.
Proof.
  induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ]; intros parent role me.
  1,2,3,4,6,8: reflexivity.
  all: cbn [GoIndex.occs_expr forallb];
       unfold occ_local_ok at 1; cbn [snd GoIndex.view_expr GoIndex.occurrence_view];
       cbn [local_conv_failure]; cbn [const_info];
       specialize (IHx me GoIndex.RConversionOperand (Pos.succ me));
       destruct (const_info x) as [ci|] eqn:Ex;
       [ destruct (convert_const _ ci) as [ci'|] eqn:Ec;
         [ cbn [andb]; rewrite IHx; reflexivity
         | cbn [andb option_map]; reflexivity ]
       | cbn [andb option_map]; rewrite IHx; reflexivity ].
Qed.

Lemma forallb_andb {A} (f g : A -> bool) (l : list A) :
  forallb (fun x => f x && g x) l = forallb f l && forallb g l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH.
  destruct (f a), (g a), (forallb f l), (forallb g l); reflexivity.
Qed.

(** a conversion-operand occurrence is always default-OK (only a println-arg root can default-fail). *)
Lemma occ_default_ok_operand : forall e par sub,
  occ_default_ok (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) GoIndex.RConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occ_default_ok_operand_true : forall e parent me,
  forallb (fun x => occ_default_ok (snd x)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = true.
Proof.
  induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ];
    intros parent me; cbn [GoIndex.occs_expr forallb snd]; rewrite occ_default_ok_operand.
  1,2,3,4,6,8: reflexivity.
  all: rewrite Bool.andb_true_l; apply IHx.
Qed.

(** a println-argument root occurrence is default-OK IFF its untyped constant defaults (typed / failed = OK). *)
Lemma occ_default_ok_printlnarg : forall e par aidx sub,
  occ_default_ok (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) (GoIndex.RPrintlnArg aidx) sub)
  = match const_info e with Some (CIUntyped c) => match default_const c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e par aidx sub. unfold occ_default_ok.
  cbn [GoIndex.view_expr GoIndex.occurrence_view arg_default_failure GoIndex.occurrence_role].
  destruct (const_info e) as [[c|t tc]|]; [ destruct (default_const c) | | ]; reflexivity.
Qed.

Lemma occ_default_fold_arg : forall e parent aidx me,
  forallb (fun x => occ_default_ok (snd x)) (GoIndex.occs_expr parent (GoIndex.RPrintlnArg aidx) me e)
  = match const_info e with Some (CIUntyped c) => match default_const c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e parent aidx me. destruct e as [ b|n1|n2|s| it x|df|ft x|dcx|ct x ];
    cbn [GoIndex.occs_expr forallb snd].
  1,2,3,4,6,8: rewrite Bool.andb_true_r; apply occ_default_ok_printlnarg.
  all: rewrite occ_default_ok_operand_true, Bool.andb_true_r; apply occ_default_ok_printlnarg.
Qed.

(** ONE println argument's occurrence stream emits nothing IFF the argument resolves ([expr_typedb]). *)
Lemma occ_emits_arg : forall e parent aidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_arg parent aidx me e) = expr_typedb UsePrintlnArg e.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg, occ_emits_none_pure.
  rewrite forallb_andb, conv_ok_fold, occ_default_fold_arg.
  unfold expr_typedb, resolve_expr, resolve_expr_const.
  destruct (const_info e) as [[c|t tc]|]; cbn [resolve_const_info].
  - destruct (default_const c) as [rc|]; cbn [option_map]; [ rewrite use_allowsb_println_true |]; reflexivity.
  - cbn [option_map]. rewrite use_allowsb_println_true. reflexivity.
  - cbn [option_map]. reflexivity.
Qed.

Lemma occ_emits_args : forall es parent aidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_args parent aidx me es)
  = forallb (expr_typedb UsePrintlnArg) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [GoIndex.occs_args]. rewrite forallb_app, occ_emits_arg, IH. reflexivity.
Qed.

Lemma occ_emits_stmt : forall s parent sidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_stmt parent sidx me s) = stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [GoIndex.occs_stmt forallb occ_emits_none_pure occ_local_ok occ_default_ok snd
       GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_args. reflexivity.
Qed.

Lemma occ_emits_stmts : forall ss parent sidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_stmts parent sidx me ss) = forallb stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [GoIndex.occs_stmts]. rewrite forallb_app, occ_emits_stmt, IH. reflexivity.
Qed.

Lemma occ_emits_decl : forall d parent didx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_decl parent didx me d) = decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [GoIndex.occs_decl forallb occ_emits_none_pure occ_local_ok occ_default_ok snd
       GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_stmts. reflexivity.
Qed.

Lemma occ_emits_decls : forall ds parent didx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_decls parent didx me ds) = forallb decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [GoIndex.occs_decls]. rewrite forallb_app, occ_emits_decl, IH. reflexivity.
Qed.

Lemma occ_emits_file : forall f,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_file f) = source_file_typedb f.
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  cbn [forallb occ_emits_none_pure occ_local_ok occ_default_ok snd GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_decls. unfold source_file_typedb, file_typedb. reflexivity.
Qed.

(** lift the file-level emit fold to the whole program (via the §19 traversal projection). *)
Lemma visit_file_emits {p} (fr : GoIndex.Snap.FileRef p) :
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.Snap.visit_file fr)
  = source_file_typedb (GoIndex.Snap.file_ref_source fr).
Proof.
  rewrite GoTypes.forallb_map_snd, GoIndex.Snap.visit_file_snd, <- GoTypes.forallb_map_snd.
  apply occ_emits_file.
Qed.

Lemma emits_none_program_typedb (p : GoProgram) :
  forallb (fun x => occ_emits_none_pure (snd x)) (prog_visit p) = program_typedb p.
Proof.
  rewrite prog_visit_flat_map, forallb_flat_map. unfold program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_emits, Hsrc. reflexivity.
Qed.

(** every program-visited occurrence IS its reference's exact source occurrence. *)
Lemma prog_visit_view (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) -> occ = GoIndex.Snap.source_occurrence_of_ref r.
Proof.
  rewrite prog_visit_flat_map. intro Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hin]].
  unfold binding_visit in Hin. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _]. exact Hocc.
Qed.

(** per-occurrence: the emitted diagnostics are empty IFF the occurrence emits nothing (pure). *)
Lemma occ_expr_diags_empty {p} (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  (occ_expr_diags idx outer (r, occ) = nil <-> occ_emits_none_pure occ = true).
Proof.
  intro Hin. pose proof (prog_visit_view p r occ Hin) as Hocc.
  unfold occ_expr_diags, occ_emits_none_pure, occ_local_ok, occ_default_ok, GoIndex.as_expr, GoIndex.as_kind.
  cbn [fst snd].
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [Hk|Hk].
  - assert (Hke : GoIndex.occurrence_kind occ = GoIndex.KExpression).
    { rewrite Hocc, <- (GoIndex.Snap.node_kind_matches_source p idx r). exact Hk. }
    destruct (GoIndex.kind_view_expr occ Hke) as [e Hve]. rewrite Hve.
    destruct (local_conv_failure e) as [[t ci]|]; cbn [andb];
      [ | destruct (arg_default_failure occ e) as [[c dt]|]; cbn [andb] ];
      split; intro H; try discriminate H; reflexivity.
  - assert (Hkne : GoIndex.occurrence_kind occ <> GoIndex.KExpression).
    { intro Hc. apply Hk. rewrite (GoIndex.Snap.node_kind_matches_source p idx r), <- Hocc. exact Hc. }
    assert (Hve : GoIndex.view_expr occ = None).
    { destruct (GoIndex.view_expr occ) as [e|] eqn:E; [| reflexivity].
      exfalso. apply Hkne. exact (GoIndex.view_expr_kind occ e E). }
    rewrite Hve. split; intro H; try discriminate H; reflexivity.
Qed.

Lemma flat_map_nil_forallb {A B} (g : A -> list B) (l : list A) :
  flat_map g l = nil <-> forallb (fun x => match g x with nil => true | _ => false end) l = true.
Proof.
  induction l as [|a l IH]; [split; reflexivity|].
  simpl. destruct (g a) as [|b gb] eqn:Ega; simpl.
  - exact IH.
  - split; intro H; discriminate H.
Qed.

(** THE EXPRESSION COMPLETENESS: [expr_diags] is empty IFF the program types ([ProgramTyped]). *)
Lemma expr_diags_empty_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  expr_diags idx = nil <-> program_typedb p = true.
Proof.
  rewrite expr_diags_eq_spec. rewrite flat_map_nil_forallb, <- emits_none_program_typedb.
  rewrite !forallb_forall. split; intro H.
  - intros [r occ] Hin.
    assert (Hroc : exists ctx, In ((r, occ), ctx) (annotate_program idx)).
    { rewrite <- (annotate_program_fst idx) in Hin. apply in_map_iff in Hin. destruct Hin as [[ro ctx] [Hf Hi]].
      cbn [fst] in Hf. subst ro. exists ctx. exact Hi. }
    destruct Hroc as [ctx Hroc]. specialize (H _ Hroc). cbn [fst snd] in H.
    apply (occ_expr_diags_empty idx ctx r occ Hin).
    destruct (occ_expr_diags idx ctx (r, occ)); [reflexivity | discriminate H].
  - intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
    assert (Hin' : In (r, occ) (prog_visit p)).
    { rewrite <- (annotate_program_fst idx). exact (in_map fst _ _ Hin). }
    specialize (H (r, occ) Hin'). cbn [snd] in H.
    apply (occ_expr_diags_empty idx ctx r occ Hin') in H. rewrite H. reflexivity.
Qed.

(* ---- PACKAGE main-count relation: # of top-level-decl occurrences per file = [file_main_count] ---- *)

Definition occ_main_count (occ : GoIndex.SourceOccurrence) : nat :=
  match GoIndex.occurrence_role occ with GoIndex.RFileDecl _ => 1 | _ => 0 end.
Definition sum_main {A} (l : list (A * GoIndex.SourceOccurrence)) : nat :=
  fold_right (fun (ro : A * GoIndex.SourceOccurrence) (acc : nat) => (occ_main_count (snd ro) + acc)%nat) 0%nat l.

Lemma sum_main_cons {A} (x : A * GoIndex.SourceOccurrence) (l : list (A * GoIndex.SourceOccurrence)) :
  sum_main (x :: l) = (occ_main_count (snd x) + sum_main l)%nat.
Proof. reflexivity. Qed.

Lemma sum_main_app {A} (a b : list (A * GoIndex.SourceOccurrence)) :
  sum_main (a ++ b) = (sum_main a + sum_main b)%nat.
Proof.
  induction a as [|x a IH]; [reflexivity|].
  rewrite <- app_comm_cons, (sum_main_cons x (a ++ b)), (sum_main_cons x a), IH. lia.
Qed.

Lemma sum_main_operand : forall e parent me,
  sum_main (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = 0%nat.
Proof.
  induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ]; intros parent me;
    cbn [GoIndex.occs_expr]; rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  1,2,3,4,6,8: reflexivity.
  all: rewrite Nat.add_0_l; apply IHx.
Qed.

Lemma sum_main_arg : forall e parent aidx me, sum_main (GoIndex.occs_arg parent aidx me e) = 0%nat.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b|n1|n2|s| it x|df|ft x|dcx|ct x ];
    cbn [GoIndex.occs_expr]; rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  1,2,3,4,6,8: reflexivity.
  all: rewrite Nat.add_0_l; apply sum_main_operand.
Qed.

Lemma sum_main_args : forall es parent aidx me, sum_main (GoIndex.occs_args parent aidx me es) = 0%nat.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [GoIndex.occs_args]. rewrite sum_main_app, sum_main_arg, IH. reflexivity.
Qed.

Lemma sum_main_stmt : forall s parent sidx me, sum_main (GoIndex.occs_stmt parent sidx me s) = 0%nat.
Proof.
  intros [args] parent sidx me. cbn [GoIndex.occs_stmt].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite Nat.add_0_l. apply sum_main_args.
Qed.

Lemma sum_main_stmts : forall ss parent sidx me, sum_main (GoIndex.occs_stmts parent sidx me ss) = 0%nat.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [GoIndex.occs_stmts]. rewrite sum_main_app, sum_main_stmt, IH. reflexivity.
Qed.

Lemma sum_main_decl : forall d parent didx me, sum_main (GoIndex.occs_decl parent didx me d) = 1%nat.
Proof.
  intros [body] parent didx me. cbn [GoIndex.occs_decl].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_stmts. reflexivity.
Qed.

Lemma sum_main_decls : forall ds parent didx me, sum_main (GoIndex.occs_decls parent didx me ds) = length ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [GoIndex.occs_decls length]. rewrite sum_main_app, sum_main_decl, IH. reflexivity.
Qed.

Lemma file_main_count_length : forall decls, file_main_count decls = length decls.
Proof.
  intro decls. unfold file_main_count.
  induction decls as [|[body] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sum_main_file : forall f, sum_main (GoIndex.occs_file f) = file_main_count (source_decls f).
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_decls, file_main_count_length. reflexivity.
Qed.

(* ============================================================================================================
   §11 (C3) — PACKAGE MAIN-REF BUCKETS.  The per-file/per-package collection of the top-level-decl (main)
   occurrences as validated [DeclRef]s, in canonical order.  Its length is the declarative [file_main_count]
   (hence, aggregated, [ps_main_count]) — so the reference collection AGREES with the package count judgment,
   without a second production package decision.

   [decl_kind_count] counts an occurrence by its KIND (KTopLevelDecl); [occ_main_count] counts by its ROLE
   (RFileDecl).  Over a real occurrence stream ([occs_file]) the two coincide (a decl head is the ONLY
   KTopLevelDecl and the ONLY RFileDecl), so a DeclRef minted on kind counts exactly the main declarations.
   ============================================================================================================ *)

Definition decl_kind_count (o : GoIndex.SourceOccurrence) : nat :=
  match GoIndex.occurrence_kind o with GoIndex.KTopLevelDecl => 1%nat | _ => 0%nat end.

Definition decl_count_list {A} (l : list (A * GoIndex.SourceOccurrence)) : nat :=
  fold_right (fun (ro : A * GoIndex.SourceOccurrence) (acc : nat) => (decl_kind_count (snd ro) + acc)%nat) 0%nat l.

Lemma decl_count_list_cons {A} (x : A * GoIndex.SourceOccurrence) (l : list (A * GoIndex.SourceOccurrence)) :
  decl_count_list (x :: l) = (decl_kind_count (snd x) + decl_count_list l)%nat.
Proof. reflexivity. Qed.

Lemma decl_count_list_app {A} (a b : list (A * GoIndex.SourceOccurrence)) :
  decl_count_list (a ++ b) = (decl_count_list a + decl_count_list b)%nat.
Proof.
  induction a as [|x a IH]; [reflexivity|].
  rewrite <- app_comm_cons, (decl_count_list_cons x (a ++ b)), (decl_count_list_cons x a), IH. lia.
Qed.

(** [decl_count_list] depends only on the OCCURRENCE component (the [snd]-projection). *)
Lemma decl_count_list_snd {A B} (l1 : list (A * GoIndex.SourceOccurrence)) (l2 : list (B * GoIndex.SourceOccurrence)) :
  map snd l1 = map snd l2 -> decl_count_list l1 = decl_count_list l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] Hm; cbn [map] in Hm; try discriminate; [reflexivity|].
  injection Hm as Hsnd Hrest.
  rewrite (decl_count_list_cons x l1), (decl_count_list_cons y l2), Hsnd, (IH l2 Hrest). reflexivity.
Qed.

(* ---- kind/role COHERENCE over a real occurrence stream: [decl_kind_count o = occ_main_count o]. ---- *)

Definition coh (o : GoIndex.SourceOccurrence) : Prop := decl_kind_count o = occ_main_count o.

Lemma coh_operand : forall e parent me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e).
Proof.
  induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ]; intros parent me; cbn [GoIndex.occs_expr].
  1,2,3,4,6,8: constructor; [ reflexivity | constructor ].
  all: constructor; [ reflexivity | apply IHx ].
Qed.

Lemma coh_arg : forall e parent aidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_arg parent aidx me e).
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b|n1|n2|s| it x|df|ft x|dcx|ct x ]; cbn [GoIndex.occs_expr].
  1,2,3,4,6,8: constructor; [ reflexivity | constructor ].
  all: constructor; [ reflexivity | apply coh_operand ].
Qed.

Lemma coh_args : forall es parent aidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_args parent aidx me es).
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [constructor|].
  cbn [GoIndex.occs_args]. apply Forall_app. split; [ apply coh_arg | apply IH ].
Qed.

Lemma coh_stmt : forall s parent sidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_stmt parent sidx me s).
Proof.
  intros [args] parent sidx me. cbn [GoIndex.occs_stmt].
  constructor; [ reflexivity | apply coh_args ].
Qed.

Lemma coh_stmts : forall ss parent sidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_stmts parent sidx me ss).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [constructor|].
  cbn [GoIndex.occs_stmts]. apply Forall_app. split; [ apply coh_stmt | apply IH ].
Qed.

Lemma coh_decl : forall d parent didx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_decl parent didx me d).
Proof.
  intros [body] parent didx me. cbn [GoIndex.occs_decl].
  constructor; [ reflexivity | apply coh_stmts ].
Qed.

Lemma coh_decls : forall ds parent didx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_decls parent didx me ds).
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [constructor|].
  cbn [GoIndex.occs_decls]. apply Forall_app. split; [ apply coh_decl | apply IH ].
Qed.

Lemma coh_file : forall f, Forall (fun ro => coh (snd ro)) (GoIndex.occs_file f).
Proof.
  intro f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  constructor; [ reflexivity | ]. constructor; [ reflexivity | apply coh_decls ].
Qed.

(** the COHERENCE, transported to the [snd]-count identity: [decl_count_list = sum_main] over a file's occurrences. *)
Lemma decl_count_sum_main_file : forall f, decl_count_list (GoIndex.occs_file f) = sum_main (GoIndex.occs_file f).
Proof.
  intro f. pose proof (coh_file f) as Hcoh.
  induction (GoIndex.occs_file f) as [|x l IH]; [reflexivity|].
  inversion Hcoh as [|? ? Hx Hl]; subst.
  rewrite (decl_count_list_cons x l), (sum_main_cons x l), (IH Hl). unfold coh in Hx. rewrite Hx. reflexivity.
Qed.

(* the optional-bucket length, and its rewrite past the [Some l => l | None => []] read shape — the shared
   arithmetic helpers the package-bucket fold characterization below reasons through. *)
Definition olen {A} (o : option (list A)) : nat := match o with Some l => length l | None => 0%nat end.

Lemma olen_match {A} (o : option (list A)) :
  length (match o with Some l => l | None => [] end) = olen o.
Proof. destruct o; reflexivity. Qed.

(* ============================================================================================================
   §14/§28 (C3) — the PACKAGE main-ref buckets built as ONE fold over the DELIVERED visit stream (NOT a second
   per-file [Snap.visit_file]).  Each occurrence contributes to its file's package ([occ_pkg] = the file's
   parent directory): a [DMain] declaration prepends its [DeclRef]; a FILE ROOT ([KFile]) INITIALIZES the
   package entry (so a package with zero mains is still represented) without disturbing existing mains.  Since
   [prog_visit] visits each file's root then its decls in preorder, and [fold_right] processes the stream
   right-to-left, a package's bucket ends up its files' mains in canonical stream order.
   ============================================================================================================ *)

Definition occ_pkg {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : string :=
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (fst ro))).

Definition ppkg_step {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (acc : PM.t (list (GoIndex.DeclRef p)))
  : PM.t (list (GoIndex.DeclRef p)) :=
  match GoIndex.as_decl idx (fst ro) with
  | Some dr => PM.add (occ_pkg ro) (dr :: match PM.find (occ_pkg ro) acc with Some l => l | None => [] end) acc
  | None =>
      match GoIndex.as_kind idx (fst ro) GoIndex.KFile with
      | Some _ => match PM.find (occ_pkg ro) acc with Some _ => acc | None => PM.add (occ_pkg ro) [] acc end
      | None => acc
      end
  end.

Definition prog_package_refs {p} (idx : GoIndex.Snap.SyntaxIndex p) : PM.t (list (GoIndex.DeclRef p)) :=
  fold_right (ppkg_step idx) (PM.empty (list (GoIndex.DeclRef p))) (prog_visit p).

(* the per-package DMain count over an occurrence list (an occurrence contributes 1 exactly when its file's
   package is [dir] AND it mints a DeclRef). *)
Fixpoint pkg_declcount {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) : nat :=
  match l with
  | [] => 0%nat
  | ro :: rest =>
      ((if String.eqb (occ_pkg ro) dir
        then match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
       + pkg_declcount idx dir rest)%nat
  end.

(* the per-step bucket-length contribution: exactly the DMain-count contribution (a file-root init adds an
   empty bucket — presence, not length). *)
Lemma ppkg_step_olen {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  olen (PM.find dir (ppkg_step idx ro acc))
  = ((if String.eqb (occ_pkg ro) dir then match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
     + olen (PM.find dir acc))%nat.
Proof.
  unfold ppkg_step. destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. cbn [olen length]. rewrite <- Edir, olen_match. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l|] eqn:Efind.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; rewrite Edir in Efind; rewrite Efind | ]; reflexivity.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. cbn [olen length].
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Lemma ppkg_olen_char {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  olen (PM.find dir (fold_right (ppkg_step idx) acc l)) = (pkg_declcount idx dir l + olen (PM.find dir acc))%nat.
Proof.
  induction l as [|ro rest IH]; intros acc dir; [reflexivity|].
  cbn [fold_right pkg_declcount]. rewrite (ppkg_step_olen idx ro (fold_right (ppkg_step idx) acc rest) dir).
  rewrite (IH acc dir). lia.
Qed.

(* on a VISITED occurrence the DeclRef-mint contribution equals its [decl_kind_count]. *)
Lemma ppkg_as_decl_kind_count {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p)
  (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence) :
  In (r, occ) (GoIndex.Snap.visit_file fr) ->
  (match GoIndex.as_decl idx r with Some _ => 1%nat | None => 0%nat end) = decl_kind_count occ.
Proof.
  intro Hin. pose proof (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _].
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.occurrence_kind occ)
    by (rewrite (GoIndex.Snap.node_kind_matches_source p idx r), Hocc; reflexivity).
  unfold GoIndex.as_decl, GoIndex.as_kind, decl_kind_count.
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KTopLevelDecl) as [He|Hne].
  - rewrite Hk in He; rewrite He; reflexivity.
  - rewrite Hk in Hne. destruct (GoIndex.occurrence_kind occ); try reflexivity. exfalso; apply Hne; reflexivity.
Qed.

(* over a list all of whose occurrences share package [D] and mint DeclRefs by kind, the DMain-count is the
   whole [decl_count_list] when [D = dir], else 0. *)
Lemma pkg_declcount_uniform {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir D : string)
  (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  (forall ro, In ro L -> occ_pkg ro = D) ->
  (forall ro, In ro L -> match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end = decl_kind_count (snd ro)) ->
  pkg_declcount idx dir L = (if String.eqb D dir then decl_count_list L else 0%nat).
Proof.
  induction L as [|ro rest IH]; intros Hpkg Hkind.
  - cbn [pkg_declcount decl_count_list]. destruct (String.eqb D dir); reflexivity.
  - cbn [pkg_declcount]. rewrite decl_count_list_cons.
    rewrite (Hpkg ro (or_introl eq_refl)), (Hkind ro (or_introl eq_refl)).
    rewrite (IH (fun ro' Hr => Hpkg ro' (or_intror Hr)) (fun ro' Hr => Hkind ro' (or_intror Hr))).
    destruct (String.eqb D dir); lia.
Qed.

(* within a file block every occurrence has the same package ([fp_parent] of the file path); the block's
   DMain-count is the file's [file_main_count] when the package matches, else 0. *)
Lemma pkg_declcount_binding {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) (dir : string) :
  In b (GoAST.file_bindings (prog_files p)) ->
  pkg_declcount idx dir (binding_visit p b)
  = (if String.eqb (fp_parent (fst b)) dir then file_main_count (source_decls (snd b)) else 0%nat).
Proof.
  intro Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop.
  rewrite (pkg_declcount_uniform idx dir (fp_parent (GoIndex.Snap.file_ref_path fr)) (GoIndex.Snap.visit_file fr)).
  - rewrite Hpath. destruct (String.eqb (fp_parent (fst b)) dir) eqn:E; [| reflexivity].
    rewrite (decl_count_list_snd (GoIndex.Snap.visit_file fr) (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr))
               (GoIndex.Snap.visit_file_snd p fr)).
    rewrite decl_count_sum_main_file, sum_main_file, Hsrc. reflexivity.
  - intros [r occ] Hin. unfold occ_pkg; cbn [fst].
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
  - intros [r occ] Hin. cbn [fst snd]. exact (ppkg_as_decl_kind_count idx fr r occ Hin).
Qed.

Lemma pkg_declcount_app {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string)
  (l1 l2 : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  pkg_declcount idx dir (l1 ++ l2) = (pkg_declcount idx dir l1 + pkg_declcount idx dir l2)%nat.
Proof. induction l1 as [|ro l1 IH]; cbn [pkg_declcount app]; [reflexivity | rewrite IH; lia]. Qed.

(* the WHOLE-PROGRAM DMain count per package, over the retained visit stream, IS the declarative
   [pkg_main_count] (= [list_dir_count] over the file bindings). *)
Lemma pkg_declcount_prog_visit {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string) :
  pkg_declcount idx dir (prog_visit p) = pkg_main_count dir (prog_files p).
Proof.
  rewrite prog_visit_flat_map. unfold pkg_main_count.
  assert (H : forall L, (forall b, In b L -> In b (GoAST.file_bindings (prog_files p))) ->
             pkg_declcount idx dir (flat_map (binding_visit p) L) = list_dir_count dir L).
  { induction L as [|b rest IHL]; intro Hsub; [reflexivity|].
    cbn [flat_map list_dir_count]. rewrite pkg_declcount_app.
    rewrite (pkg_declcount_binding idx b dir (Hsub b (or_introl eq_refl))).
    rewrite (IHL (fun b' Hb' => Hsub b' (or_intror Hb'))). reflexivity. }
  apply H; intros b Hb; exact Hb.
Qed.

(** BUCKET LENGTH EXACTNESS (from the ONE visit-stream fold): a present bucket's length is the package's
    declarative main count [pkg_main_count]. *)
Lemma prog_package_refs_bucket_len {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (prog_package_refs idx) = Some l -> length l = pkg_main_count dir (prog_files p).
Proof.
  intros dir l Hfind.
  assert (Holen : olen (PM.find dir (prog_package_refs idx)) = pkg_main_count dir (prog_files p)).
  { unfold prog_package_refs. rewrite (ppkg_olen_char idx (prog_visit p) (PM.empty _) dir).
    rewrite PMF.empty_o. cbn [olen]. rewrite Nat.add_0_r. exact (pkg_declcount_prog_visit idx dir). }
  rewrite Hfind in Holen. cbn [olen] in Holen. exact Holen.
Qed.

(* an occurrence CONTRIBUTES its package to the bucket map iff it mints a DeclRef OR is a file root. *)
Definition ppkg_contributes {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : Prop :=
  GoIndex.as_decl idx (fst ro) <> None \/ GoIndex.as_kind idx (fst ro) GoIndex.KFile <> None.

Lemma ppkg_step_some {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  PM.find dir (ppkg_step idx ro acc) <> None
  <-> ((occ_pkg ro = dir /\ ppkg_contributes idx ro) \/ PM.find dir acc <> None).
Proof.
  unfold ppkg_step, ppkg_contributes.
  destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
    + rewrite He, PMF.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | left; discriminate] | intros _; discriminate ].
    + rewrite PMF.add_neq_o by exact Hne. split.
      * intro H; right; exact H.
      * intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l|] eqn:Efind.
      * split.
        -- intro H; right; exact H.
        -- intros [[He _]|H]; [ rewrite He in Efind; rewrite Efind; discriminate | exact H ].
      * destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
        -- rewrite He, PMF.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | right; discriminate] | intros _; discriminate ].
        -- rewrite PMF.add_neq_o by exact Hne. split.
           ++ intro H; right; exact H.
           ++ intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
    + split.
      * intro H; right; exact H.
      * intros [[_ [Hd|Hf]]|H]; [ exfalso; apply Hd; reflexivity | exfalso; apply Hf; reflexivity | exact H ].
Qed.

Lemma ppkg_find_some_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  PM.find dir (fold_right (ppkg_step idx) acc l) <> None
  <-> ((exists ro, In ro l /\ occ_pkg ro = dir /\ ppkg_contributes idx ro) \/ PM.find dir acc <> None).
Proof.
  induction l as [|ro rest IH]; intros acc dir.
  - cbn [fold_right]. split; [ intro H; right; exact H | intros [[ro' [[] _]]|H]; exact H ].
  - cbn [fold_right]. rewrite (ppkg_step_some idx ro (fold_right (ppkg_step idx) acc rest) dir), (IH acc dir). split.
    + intros [Hstep|[[ro' [Hin' Hc']]|Hacc]].
      * left; exists ro; split; [left; reflexivity | exact Hstep].
      * left; exists ro'; split; [right; exact Hin' | exact Hc'].
      * right; exact Hacc.
    + intros [[ro' [[<-|Hin'] Hc']]|Hacc].
      * left; exact Hc'.
      * right; left; exists ro'; split; [exact Hin' | exact Hc'].
      * right; right; exact Hacc.
Qed.

(* the file ROOT is a [KFile] occurrence (so a file always contributes its package's presence). *)
Lemma root_node_kind {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  GoIndex.Snap.node_kind idx (GoIndex.Snap.file_root_ref fr) = GoIndex.KFile.
Proof.
  rewrite (GoIndex.Snap.node_kind_matches_source p idx (GoIndex.Snap.file_root_ref fr)).
  pose proof (GoIndex.Snap.source_occ_of_ref_eq (GoIndex.Snap.file_root_ref fr)) as Hso.
  rewrite (GoIndex.Snap.file_root_ref_file p fr), (GoIndex.Snap.file_root_ref_local p fr) in Hso.
  assert (Hroot : In (GoIndex.root_id, GoIndex.mkOcc GoIndex.KFile (GoIndex.ViewFile (GoIndex.Snap.file_ref_source fr))
                        None GoIndex.RFileRoot (GoIndex.count_file (GoIndex.Snap.file_ref_source fr)))
                     (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr))).
  { unfold GoIndex.occs_file. destruct (source_imports (GoIndex.Snap.file_ref_source fr)) as [|i tl]; [| destruct i].
    left; reflexivity. }
  apply GoIndex.occs_file_exact in Hroot. rewrite Hso in Hroot. injection Hroot as Heq. rewrite Heq. reflexivity.
Qed.

Lemma root_ref_contributes {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  ppkg_contributes idx (GoIndex.Snap.file_root_ref fr, GoIndex.Snap.source_occurrence_of_ref (GoIndex.Snap.file_root_ref fr)).
Proof.
  right. cbn [fst]. unfold GoIndex.as_kind.
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx (GoIndex.Snap.file_root_ref fr)) GoIndex.KFile) as [He|Hne];
    [ discriminate | exfalso; apply Hne; apply root_node_kind ].
Qed.

(** DOMAIN EXACTNESS (from the ONE visit-stream fold): a bucket is present iff a file has that parent directory. *)
Lemma prog_package_refs_present {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir,
  PM.In dir (prog_package_refs idx) <-> list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true.
Proof.
  intro dir. rewrite PMF.in_find_iff. unfold prog_package_refs.
  rewrite (ppkg_find_some_iff idx (prog_visit p) (PM.empty _) dir). rewrite PMF.empty_o. split.
  - intros [[[r occ] [Hin [Hpkg _]]]|Hne]; [| exfalso; apply Hne; reflexivity].
    (* the occurrence's file is in prog_files with parent dir *)
    rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
    unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [_ Hfile].
    unfold occ_pkg in Hpkg. cbn [fst] in Hpkg. rewrite Hfile, (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef) in Hpkg.
    unfold list_dir_mem. apply existsb_exists. exists b. split; [exact Hb | apply String.eqb_eq; exact Hpkg].
  - intro Hmem. unfold list_dir_mem in Hmem. apply existsb_exists in Hmem. destruct Hmem as [b [Hb He]].
    apply String.eqb_eq in He.
    left. pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
    destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath _]]].
    exists (GoIndex.Snap.file_root_ref fr, GoIndex.Snap.source_occurrence_of_ref (GoIndex.Snap.file_root_ref fr)).
    split; [ | split; [ | apply root_ref_contributes ] ].
    + apply noderef_in_prog_visit.
    + unfold occ_pkg. cbn [fst]. rewrite (GoIndex.Snap.file_root_ref_file p fr), Hpath. exact He.
Qed.

(** BELONGS: a main DeclRef in a package's bucket belongs to THAT package (its file's parent = the key). *)
Lemma ppkg_mem {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir d,
  In d (match PM.find dir (fold_right (ppkg_step idx) acc l) with Some x => x | None => [] end) ->
  (exists ro, In ro l /\ occ_pkg ro = dir /\ GoIndex.as_decl idx (fst ro) = Some d)
  \/ In d (match PM.find dir acc with Some x => x | None => [] end).
Proof.
  induction l as [|ro rest IH]; intros acc dir d Hin; [right; exact Hin|].
  cbn [fold_right] in Hin. unfold ppkg_step at 1 in Hin.
  destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
    + rewrite He, PMF.add_eq_o in Hin by reflexivity. destruct Hin as [<-|Hin].
      * left; exists ro; split; [left; reflexivity | split; [exact He | exact Ed]].
      * destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
          [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
    + rewrite PMF.add_neq_o in Hin by exact Hne.
      destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
        [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
  - assert (Hin' : In d (match PM.find dir (fold_right (ppkg_step idx) acc rest) with Some x => x | None => [] end)).
    { destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|];
      [ destruct (PM.find (occ_pkg ro) (fold_right (ppkg_step idx) acc rest)) eqn:Efind;
        [ exact Hin | destruct (string_dec (occ_pkg ro) dir) as [He|Hne];
          [ rewrite He, PMF.add_eq_o in Hin by reflexivity; rewrite <- He, Efind; exact Hin
          | rewrite PMF.add_neq_o in Hin by exact Hne; exact Hin ] ]
      | exact Hin ]. }
    destruct (IH acc dir d Hin') as [[ro' [Hin2 [Hp' Hd']]]|Hrest];
      [ left; exists ro'; split; [right; exact Hin2 | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
Qed.

Lemma prog_package_refs_belongs {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (prog_package_refs idx) = Some l ->
  forall d, In d l ->
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref d))) = dir.
Proof.
  intros dir l Hfind d Hin.
  assert (Hb : In d (match PM.find dir (prog_package_refs idx) with Some x => x | None => [] end))
    by (rewrite Hfind; exact Hin).
  unfold prog_package_refs in Hb.
  destruct (ppkg_mem idx (prog_visit p) (PM.empty _) dir d Hb) as [[ro [_ [Hp Hd]]]|Hempty];
    [ | rewrite PMF.empty_o in Hempty; destruct Hempty ].
  rewrite (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl d Hd). exact Hp.
Qed.

Lemma prog_package_refs_singleton_on_success {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  AllPackagesOneMain p -> forall dir l,
  PM.find dir (prog_package_refs idx) = Some l -> exists d, l = [d].
Proof.
  intros Hall dir l Hfind.
  pose proof (prog_package_refs_bucket_len idx dir l Hfind) as Hlen.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { apply (prog_package_refs_present idx dir). apply PMF.in_find_iff. rewrite Hfind. discriminate. }
  assert (Hmt : PM.MapsTo dir (mkPkgSummary (pkg_main_count dir (prog_files p))) (package_summaries (prog_files p))).
  { apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (Hall dir _ Hmt) as Hone. cbn [ps_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(* ============================================================================================================
   §8 (C3) — the PACKAGE diagnostics.  Every package with a main count other than one is a failure; the anchor
   is a validated [PackageRef] (each package in [package_summaries] is represented, so the reference is real).
   Emptiness is tied DIRECTLY to [pkg_all_ok] (the package half of the decision).
   (ROOT emits [DRMissingMain] for every non-conforming package; a later refinement distinguishes the duplicate
   case with [DRDuplicateMain] over the collected main [DeclRef]s.)
   ============================================================================================================ *)

(* A non-conforming package is diagnosed with STRUCTURED reasons anchored in the exact snapshot:
   - n >= 2 mains -> n-1 [DRDuplicateMain], one per TAIL main [d2, d3, ...] each related to the FIRST canonical
     main [d1] ([later_primary] = the redundant tail main; [earlier_related] = the first main);
   - zero mains -> [DRMissingMain] anchored at the validated [PackageRef].
   The canonical bucket order (FileMap-path then local NodeKey) makes the anchors deterministic; evidence is
   never overwritten (the bucket preserves every main, and every redundant main after the first is reported). *)
(** the RETAINED-bucket package classifier: decides a package PURELY from its bucket in the retained
    [prog_package_refs] map — a bucket [d1 :: rest] emits [map (DRDuplicateMain _ d1) rest] (n-1 diagnostics,
    each redundant tail main related to the first; empty for the conforming length-1 bucket); a length-0 bucket
    emits [DRMissingMain] with the [PackageRef] built from the bucket's OWN domain membership
    ([bucket_key_present], NO [package_summaries] / [package_present_b] rescan).  [package_summaries] (the legacy
    FM.fold counter) is used ONLY to bridge the bucket lengths to [AllPackagesOneMain] ([pkg_diags_empty_iff]),
    NEVER in the decision. *)
Lemma elements_all_mapsto {p} (m : PM.t (list (GoIndex.DeclRef p))) : forall kv,
  In kv (PM.elements m) -> PM.MapsTo (fst kv) (snd kv) m.
Proof.
  intros [dir l] Hin. apply PMF.elements_mapsto_iff, InA_alt.
  exists (dir, l). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma mapsto_in_elements {p} (m : PM.t (list (GoIndex.DeclRef p))) : forall dir l,
  PM.MapsTo dir l m -> In (dir, l) (PM.elements m).
Proof.
  intros dir l Hmt. apply PMF.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
  destruct Hmt as [[dir' l'] [[Hk Hl] Hin]]. cbn in Hk, Hl. subst. exact Hin.
Qed.

Lemma bucket_key_present {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.MapsTo dir l (prog_package_refs idx) -> package_present_b p dir = true.
Proof.
  intros dir l Hmt. unfold package_present_b.
  apply (proj1 (prog_package_refs_present idx dir)). exists l. exact Hmt.
Qed.

Definition pkg_diag_of_bucket {p} (m : PM.t (list (GoIndex.DeclRef p)))
    (Hpres : forall dir l, PM.MapsTo dir l m -> package_present_b p dir = true)
    (dir : string) (l : list (GoIndex.DeclRef p)) (Hmt : PM.MapsTo dir l m)
    : list (DiagnosticReason p) :=
  match l with
  | nil        => [ DRMissingMain (mkPackageRef p dir (Hpres dir l Hmt)) ]
  | d1 :: rest => map (fun dk => DRDuplicateMain dk d1) rest
  end.

Lemma pkg_diag_of_bucket_nil_iff {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt :
  @pkg_diag_of_bucket p m Hpres dir l Hmt = nil <-> length l = 1%nat.
Proof.
  unfold pkg_diag_of_bucket; destruct l as [|d1 [|d2 rest]]; cbn [map length];
    split; intro H; solve [ reflexivity | discriminate H ].
Qed.

Fixpoint bucket_diags_elems {p} (m : PM.t (list (GoIndex.DeclRef p)))
    (Hpres : forall dir l, PM.MapsTo dir l m -> package_present_b p dir = true)
    (es : list (string * list (GoIndex.DeclRef p)))
    (Hall : forall kv, In kv es -> PM.MapsTo (fst kv) (snd kv) m)
    : list (DiagnosticReason p) :=
  match es return (forall kv, In kv es -> PM.MapsTo (fst kv) (snd kv) m) -> list (DiagnosticReason p) with
  | [] => fun _ => []
  | kv :: rest => fun H =>
      pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (H kv (or_introl eq_refl))
      ++ bucket_diags_elems m Hpres rest (fun kv' Hin => H kv' (or_intror Hin))
  end Hall.

Lemma bucket_diags_elems_nil_iff {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall :
  @bucket_diags_elems p m Hpres es Hall = nil <-> (forall kv, In kv es -> length (snd kv) = 1%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (pkg_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl)) = nil)
        by exact (proj2 (pkg_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin')) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

Definition pkg_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  bucket_diags_elems (prog_package_refs idx) (bucket_key_present idx)
    (PM.elements (prog_package_refs idx)) (elements_all_mapsto (prog_package_refs idx)).

(** THE PACKAGE COMPLETENESS: no package diagnostic IFF every package has exactly one main.  The DECISION
    reads only the retained buckets (each bucket's LENGTH); [package_summaries] appears ONLY here, bridging
    the bucket lengths to [AllPackagesOneMain] / [pkg_all_ok]. *)
Lemma pkg_diags_empty_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) : pkg_diags idx = nil <-> pkg_all_ok p = true.
Proof.
  unfold pkg_diags. rewrite bucket_diags_elems_nil_iff, pkg_all_ok_AllPackagesOneMain.
  unfold AllPackagesOneMain. split.
  - intros Hbuck dir s Hmt.
    assert (Hpres : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
    { pose proof (PM.find_1 Hmt) as Hf. rewrite package_summaries_find in Hf.
      destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:E; [ reflexivity | discriminate Hf ]. }
    destruct (proj2 (prog_package_refs_present idx dir) Hpres) as [l Hbmt].
    assert (Hlen : length l = 1%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt).
    rewrite (package_summary_main_count (prog_files p) dir s Hmt).
    rewrite <- (prog_package_refs_bucket_len idx dir l (PM.find_1 Hbmt)). exact Hlen.
  - intros Hall kv Hin.
    pose proof (elements_all_mapsto (prog_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PM.MapsTo (fst kv) (mkPkgSummary (pkg_main_count (fst kv) (prog_files p))) (package_summaries (prog_files p))).
    { apply PM.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hall (fst kv) _ Hms) as Hone. cbn [ps_main_count] in Hone.
    rewrite (prog_package_refs_bucket_len idx (fst kv) (snd kv) (PM.find_1 Hbmt)). exact Hone.
Qed.

(* ============================================================================================================
   §12/§13/§14 (C3) — the ONE retained indexed-analysis root.  [analyze] builds ONE [IndexedProgram] and returns
   either exact facts (on success) or a NONEMPTY structured diagnostic list (on failure).  The success/failure
   decision is the analysis-native [analysis_ok_b] (proved [= GoCompile]); [collect_diagnostics] gives the
   structured failure payload, nonempty exactly when the decision fails.
   ============================================================================================================ *)

Lemma app_nil_iff {A} (l1 l2 : list A) : l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof. split; [ apply app_eq_nil | intros [-> ->]; reflexivity ]. Qed.

(* ============================================================================================================
   §16 — DIAGNOSTIC STORAGE AND CANONICAL ORDER.  Node-primary diagnostics (invalid-conversion, defaulting,
   duplicate-main — each anchored at an occurrence NodeKey) are accumulated into a STANDARD [NodeKeyMapBase]
   whose bucket value is a code-ordered list (normally a singleton, but a bucket prevents a future map overwrite
   from erasing multiple diagnostics at one occurrence).  The final report flattens the map's CANONICAL elements
   (path then local id) with code-ordered bucket values, THEN appends the package-primary (missing-main)
   diagnostics in PackageMap key order.  So a duplicate-main at `a/q.go:3` correctly precedes an
   invalid-conversion at `z/main.go:5` even though the latter is discovered first.
   ============================================================================================================ *)

(* a code-ordered insertion into one occurrence's bucket (stable by the finite [DiagnosticCode] order). *)
Fixpoint sorted_insert {X} (code : X -> nat) (x : X) (l : list X) : list X :=
  match l with
  | [] => [x]
  | y :: rest => if Nat.leb (code x) (code y) then x :: l else y :: sorted_insert code x rest
  end.

Definition nkm_find {X} (k : GoIndex.NodeKey) (m : GoIndex.NodeKeyMapBase.t (list X)) : list X :=
  match GoIndex.NodeKeyMapBase.find k m with Some l => l | None => [] end.

Definition bucket_add {X} (code : X -> nat) (kx : GoIndex.NodeKey * X)
    (m : GoIndex.NodeKeyMapBase.t (list X)) : GoIndex.NodeKeyMapBase.t (list X) :=
  GoIndex.NodeKeyMapBase.add (fst kx) (sorted_insert code (snd kx) (nkm_find (fst kx) m)) m.

(* flatten node-keyed values into the NodeKeyMap-canonical order (path/local id), code-ordered inside a bucket. *)
Definition bucket_flatten {X} (code : X -> nat) (kxs : list (GoIndex.NodeKey * X)) : list X :=
  flat_map snd (GoIndex.NodeKeyMapBase.elements
    (fold_right (bucket_add code) (GoIndex.NodeKeyMapBase.empty (list X)) kxs)).

Lemma sorted_insert_nonnil {X} (code : X -> nat) (x : X) (l : list X) : sorted_insert code x l <> nil.
Proof. destruct l as [|y rest]; simpl; [discriminate | destruct (Nat.leb (code x) (code y)); discriminate]. Qed.

(* if some key maps to a nonempty bucket, the whole flatten is nonempty (that bucket's elements are included). *)
Lemma nkm_find_flat_nonempty {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (b : list X) :
  GoIndex.NodeKeyMapBase.find k m = Some b -> b <> nil ->
  flat_map snd (GoIndex.NodeKeyMapBase.elements m) <> nil.
Proof.
  intros Hf Hb.
  apply GoIndex.NodeKeyMapFacts.find_mapsto_iff, GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt in Hf.
  destruct Hf as [[k' b'] [[Hk Hb'] Hin]]. cbn in Hk, Hb'.
  intro Hnil. apply Hb. rewrite Hb'.
  assert (Hin2 : In b' (map snd (GoIndex.NodeKeyMapBase.elements m)))
    by (apply in_map_iff; exists (k', b'); split; [reflexivity | exact Hin]).
  clear -Hnil Hin2. revert Hnil Hin2. generalize (GoIndex.NodeKeyMapBase.elements m) as els.
  induction els as [|e els IH]; cbn [flat_map map]; [intros _ []|].
  intros Hnil Hin2. apply app_eq_nil in Hnil. destruct Hnil as [He Htl].
  destruct Hin2 as [<-|Hin2]; [exact He | apply IH; assumption].
Qed.

(* a nonempty keyed list flattens to a nonempty report: its first key holds a nonempty (sorted-inserted) bucket. *)
Lemma bucket_flatten_cons_nonempty {X} (code : X -> nat) (kx : GoIndex.NodeKey * X) (rest : list (GoIndex.NodeKey * X)) :
  bucket_flatten code (kx :: rest) <> nil.
Proof.
  unfold bucket_flatten. cbn [fold_right]. unfold bucket_add at 1.
  set (m := fold_right (bucket_add code) (GoIndex.NodeKeyMapBase.empty (list X)) rest).
  apply (nkm_find_flat_nonempty _ (fst kx) (sorted_insert code (snd kx) (nkm_find (fst kx) m))).
  - apply nodekeymap_add_eq.
  - apply sorted_insert_nonnil.
Qed.

Lemma bucket_flatten_nil_iff {X} (code : X -> nat) (kxs : list (GoIndex.NodeKey * X)) :
  bucket_flatten code kxs = nil <-> kxs = nil.
Proof.
  split; [ | intros ->; reflexivity ].
  destruct kxs as [|kx rest]; [reflexivity|].
  intro H. exfalso. exact (bucket_flatten_cons_nonempty code kx rest H).
Qed.

(* the node-primary key of a diagnostic (Some for the three node-anchored reasons; None for missing-main). *)
Definition diag_node_key {p} (d : DiagnosticReason p) : option GoIndex.NodeKey :=
  match diagnostic_primary d with AtNode r => Some (GoIndex.Snap.node_ref_key r) | _ => None end.
Definition dcode {p} (d : DiagnosticReason p) : nat := diagnostic_code_index (diagnostic_code d).
Definition node_keyed {p} (l : list (DiagnosticReason p)) : list (GoIndex.NodeKey * DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some k => [(k, d)] | None => [] end) l.
Definition pkg_primary {p} (l : list (DiagnosticReason p)) : list (DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some _ => [] | None => [d] end) l.

Definition collect_diagnostics (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  bucket_flatten dcode (node_keyed (expr_diags idx ++ pkg_diags idx))
  ++ pkg_primary (expr_diags idx ++ pkg_diags idx).

(* node_keyed and pkg_primary partition the diagnostics, so both empty iff the whole list is empty. *)
Lemma node_pkg_partition_nil {p} (l : list (DiagnosticReason p)) :
  node_keyed l = nil /\ pkg_primary l = nil <-> l = nil.
Proof.
  split; [ | intros ->; split; reflexivity ].
  destruct l as [|d rest]; [reflexivity|]. unfold node_keyed, pkg_primary; cbn [flat_map].
  destruct (diag_node_key d) as [k|]; cbn [app]; intros [H1 H2]; discriminate.
Qed.

Lemma collect_diagnostics_empty_iff (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  collect_diagnostics p idx = nil <-> analysis_ok_b p = true.
Proof.
  unfold collect_diagnostics. rewrite app_nil_iff, bucket_flatten_nil_iff, node_pkg_partition_nil, app_nil_iff.
  rewrite expr_diags_empty_iff, pkg_diags_empty_iff.
  unfold analysis_ok_b. rewrite Bool.andb_true_iff, expr_all_ok_program_typedb. reflexivity.
Qed.

Lemma collect_diagnostics_nonempty (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  analysis_ok_b p = false -> collect_diagnostics p idx <> nil.
Proof.
  intros H Hc. apply (collect_diagnostics_empty_iff p idx) in Hc. rewrite Hc in H. discriminate H.
Qed.

(* ---- §16/§17 — the node-bucketing COMMUTES WITH a value transform, so the ERASED report is the erased source
   diagnostics run through the SAME bucketing.  This makes the erased report a source function (deterministic,
   vm-computable), and it is the bridge for the exact §22 fixtures. ---- *)

Lemma nodekey_sorted_map_fst {A B} (f : A -> B) : forall l,
  Sorted (@GoIndex.NodeKeyMapBase.lt_key A) l ->
  Sorted (@GoIndex.NodeKeyMapBase.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma nodekeymap_map_elements {A B} (f : A -> B) (m : GoIndex.NodeKeyMapBase.t A) :
  GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (GoIndex.NodeKeyMapBase.elements m).
Proof.
  apply GoIndex.nodekey_eqlistA_eqke_eq.
  apply GoIndex.NodeKeyMapOrd.sort_equivlistA_eqlistA;
    [ apply GoIndex.NodeKeyMapBase.elements_3
    | apply nodekey_sorted_map_fst, GoIndex.NodeKeyMapBase.elements_3 | ].
  intros [k e].
  rewrite <- GoIndex.NodeKeyMapFacts.elements_mapsto_iff, GoIndex.NodeKeyMapFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. unfold GoIndex.NodeKey_OT.eq in Hk. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. unfold GoIndex.NodeKey_OT.eq in Hk. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma sorted_insert_map {X Y} (g : X -> Y) (codeX : X -> nat) (codeY : Y -> nat)
  (Hc : forall x, codeY (g x) = codeX x) (x : X) (l : list X) :
  sorted_insert codeY (g x) (map g l) = map g (sorted_insert codeX x l).
Proof.
  induction l as [|y rest IH]; cbn [map sorted_insert]; [reflexivity|].
  rewrite !Hc. destruct (Nat.leb (codeX x) (codeX y)); cbn [map]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma nkmap_map_add {A B} (h : A -> B) (k : GoIndex.NodeKey) (v : A) (m : GoIndex.NodeKeyMapBase.t A) :
  GoIndex.NodeKeyMapBase.Equal (GoIndex.NodeKeyMapBase.map h (GoIndex.NodeKeyMapBase.add k v m))
                               (GoIndex.NodeKeyMapBase.add k (h v) (GoIndex.NodeKeyMapBase.map h m)).
Proof.
  intro k'. rewrite GoIndex.NodeKeyMapFacts.map_o.
  destruct (GoIndex.NodeKey_OT.eq_dec k k') as [Heq|Hne].
  - rewrite !GoIndex.NodeKeyMapFacts.add_eq_o by exact Heq. reflexivity.
  - rewrite !GoIndex.NodeKeyMapFacts.add_neq_o by exact Hne. rewrite GoIndex.NodeKeyMapFacts.map_o. reflexivity.
Qed.

Lemma bucket_fold_map {X Y} (g : X -> Y) (codeX : X -> nat) (codeY : Y -> nat)
  (Hc : forall x, codeY (g x) = codeX x) (kxs : list (GoIndex.NodeKey * X)) :
  GoIndex.NodeKeyMapBase.Equal
    (GoIndex.NodeKeyMapBase.map (map g) (fold_right (bucket_add codeX) (GoIndex.NodeKeyMapBase.empty (list X)) kxs))
    (fold_right (bucket_add codeY) (GoIndex.NodeKeyMapBase.empty (list Y)) (map (fun kx => (fst kx, g (snd kx))) kxs)).
Proof.
  induction kxs as [|kx rest IH]; cbn [fold_right map].
  - intro k. rewrite GoIndex.NodeKeyMapFacts.map_o, !GoIndex.NodeKeyMapFacts.empty_o. reflexivity.
  - unfold bucket_add at 1 3. cbn [fst snd].
    set (M := fold_right (bucket_add codeX) (GoIndex.NodeKeyMapBase.empty (list X)) rest) in *.
    set (M' := fold_right (bucket_add codeY) (GoIndex.NodeKeyMapBase.empty (list Y))
                          (map (fun kx0 => (fst kx0, g (snd kx0))) rest)) in *.
    assert (Hfind : nkm_find (fst kx) M' = map g (nkm_find (fst kx) M)).
    { unfold nkm_find. rewrite <- (IH (fst kx)), GoIndex.NodeKeyMapFacts.map_o.
      destruct (GoIndex.NodeKeyMapBase.find (fst kx) M); reflexivity. }
    rewrite Hfind, (sorted_insert_map g codeX codeY Hc).
    transitivity (GoIndex.NodeKeyMapBase.add (fst kx)
                    (map g (sorted_insert codeX (snd kx) (nkm_find (fst kx) M))) (GoIndex.NodeKeyMapBase.map (map g) M)).
    + apply nkmap_map_add.
    + apply GoIndex.NodeKeyMapFacts.add_m; [reflexivity | reflexivity | exact IH].
Qed.

Lemma bucket_flatten_map {X Y} (g : X -> Y) (codeX : X -> nat) (codeY : Y -> nat)
  (Hc : forall x, codeY (g x) = codeX x) (kxs : list (GoIndex.NodeKey * X)) :
  map g (bucket_flatten codeX kxs) = bucket_flatten codeY (map (fun kx => (fst kx, g (snd kx))) kxs).
Proof.
  unfold bucket_flatten.
  rewrite <- (GoIndex.nodekeymap_elements_Equal _ _ (bucket_fold_map g codeX codeY Hc kxs)).
  rewrite nodekeymap_map_elements.
  generalize (GoIndex.NodeKeyMapBase.elements (fold_right (bucket_add codeX) (GoIndex.NodeKeyMapBase.empty (list X)) kxs)) as l.
  induction l as [|[k b] l IH]; cbn [flat_map map]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

(* ---- MEMBERSHIP: the bucketing preserves the multiset of values (a reordering), so the report has EXACTLY the
   diagnostics of [expr_diags ++ pkg_diags] (needed for the order-independent legacy-class projection). ---- *)

Lemma flat_map_snd_mapsto {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements m)) <->
  exists k b, GoIndex.NodeKeyMapBase.MapsTo k b m /\ In d b.
Proof.
  rewrite in_flat_map. split.
  - intros [[k b] [Hin Hd]]. cbn in Hd. exists k, b. split; [|exact Hd].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [split; reflexivity | exact Hin].
  - intros [k [b [Hmt Hd]]].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' b'] [[Hk Hb] Hin]]. cbn in Hk, Hb.
    exists (k', b'). split; [exact Hin | cbn; rewrite <- Hb; exact Hd].
Qed.

Lemma flat_map_snd_add {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (v : list X) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.add k v m))) <->
  In d v \/ In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. split.
  - intros [k' [b [Hmt Hd]]]. apply GoIndex.NodeKeyMapFacts.add_mapsto_iff in Hmt.
    destruct Hmt as [[Hk Hb]|[Hk Hmt]].
    + subst b. left; exact Hd.
    + right. exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff; split; [exact Hk|exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + exists k, v. split; [ apply GoIndex.NodeKeyMapFacts.add_mapsto_iff; left; split; reflexivity | exact Hd ].
    + apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.add_mapsto_iff; right; split; [exact Hk | exact Hmt] | exact Hd ].
Qed.

Lemma flat_map_snd_find {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements m)) <->
  In d (nkm_find k m) \/ In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. unfold nkm_find. split.
  - intros [k' [b [Hmt Hd]]]. destruct (GoIndex.NodeKey_OT.eq_dec k k') as [Hk|Hk].
    + left. apply GoIndex.NodeKeyMapFacts.find_mapsto_iff in Hmt.
      rewrite (GoIndex.NodeKeyMapFacts.find_o m Hk), Hmt. exact Hd.
    + right. exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff; split; [exact Hk | exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + destruct (GoIndex.NodeKeyMapBase.find k m) as [b0|] eqn:Ef; [ | destruct Hd ].
      exists k, b0. split; [ apply GoIndex.NodeKeyMapFacts.find_mapsto_iff; exact Ef | exact Hd ].
    + apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [exact Hmt | exact Hd].
Qed.

Lemma sorted_insert_In {X} (code : X -> nat) (x : X) (l : list X) (d : X) :
  In d (sorted_insert code x l) <-> x = d \/ In d l.
Proof.
  induction l as [|y rest IH]; cbn [sorted_insert]; [ cbn [In]; tauto |].
  destruct (Nat.leb (code x) (code y)); cbn [In]; [ tauto | rewrite IH; tauto ].
Qed.

Lemma bucket_flatten_In {X} (code : X -> nat) (kxs : list (GoIndex.NodeKey * X)) (d : X) :
  In d (bucket_flatten code kxs) <-> In d (map snd kxs).
Proof.
  unfold bucket_flatten. induction kxs as [|kx rest IH]; cbn [fold_right map].
  - rewrite flat_map_snd_mapsto. split; [ intros [k [b [Hmt _]]]; revert Hmt; apply GoIndex.NodeKeyMapFacts.empty_mapsto_iff | intros [] ].
  - unfold bucket_add at 1.
    set (M := fold_right (bucket_add code) (GoIndex.NodeKeyMapBase.empty (list X)) rest) in *.
    rewrite flat_map_snd_add, sorted_insert_In, or_assoc, <- (flat_map_snd_find M (fst kx) d), IH.
    cbn [In]. tauto.
Qed.

Lemma existsb_In_eq {A} (f : A -> bool) (l1 l2 : list A) :
  (forall x, In x l1 <-> In x l2) -> existsb f l1 = existsb f l2.
Proof.
  intro H. destruct (existsb f l1) eqn:E1; destruct (existsb f l2) eqn:E2; try reflexivity.
  - apply existsb_exists in E1. destruct E1 as [x [Hin Hf]].
    assert (Hc : existsb f l2 = true) by (apply existsb_exists; exists x; split; [apply H; exact Hin | exact Hf]).
    rewrite Hc in E2; discriminate.
  - apply existsb_exists in E2. destruct E2 as [x [Hin Hf]].
    assert (Hc : existsb f l1 = true) by (apply existsb_exists; exists x; split; [apply H; exact Hin | exact Hf]).
    rewrite Hc in E1; discriminate.
Qed.

Lemma node_pkg_In {p} (l : list (DiagnosticReason p)) (d : DiagnosticReason p) :
  In d (map snd (node_keyed l)) \/ In d (pkg_primary l) <-> In d l.
Proof.
  induction l as [|d0 rest IH]; [cbn; tauto|].
  replace (node_keyed (d0 :: rest))
    with ((match diag_node_key d0 with Some k => [(k, d0)] | None => nil end) ++ node_keyed rest) by reflexivity.
  replace (pkg_primary (d0 :: rest))
    with ((match diag_node_key d0 with Some _ => nil | None => [d0] end) ++ pkg_primary rest) by reflexivity.
  rewrite map_app, !in_app_iff. cbn [In]. destruct (diag_node_key d0) as [k|]; cbn [map In]; rewrite <- IH; tauto.
Qed.

Lemma collect_diagnostics_In {p} (idx : GoIndex.Snap.SyntaxIndex p) (d : DiagnosticReason p) :
  In d (collect_diagnostics p idx) <-> In d (expr_diags idx ++ pkg_diags idx).
Proof.
  unfold collect_diagnostics. rewrite in_app_iff, bucket_flatten_In. apply node_pkg_In.
Qed.

(** §17 (C3 FINAL) — the ERASED analysis report: the canonical diagnostic list projected through
    [erase_diagnostic], so it is a snapshot-INDEPENDENT [list ErasedDiagnostic] comparable by [=].  It is empty
    exactly when the analysis accepts (same decision as [collect_diagnostics]). *)
Definition erased_report (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list ErasedDiagnostic :=
  map erase_diagnostic (collect_diagnostics p idx).

Lemma erased_report_empty_iff (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  erased_report p idx = nil <-> analysis_ok_b p = true.
Proof.
  unfold erased_report. rewrite <- collect_diagnostics_empty_iff.
  split; [ apply map_eq_nil | intro H; rewrite H; reflexivity ].
Qed.

(* ============================================================================================================
   §16/§17 (C3 FINAL) — the KEYED visit stream is SOURCE-DETERMINED.  Erasing a visited reference to its
   NodeKey (path + local id) and pairing it with its source occurrence yields a stream that depends ONLY on the
   file map's canonical [file_bindings] and each file's [occs_file] — NO snapshot [p] survives.  This is the
   foundation for cross-snapshot report/fact determinism: [FilesEqual] programs have IDENTICAL keyed streams.
   ============================================================================================================ *)
Lemma keyed_visit_file {p} (fr : GoIndex.Snap.FileRef p) :
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (GoIndex.Snap.visit_file fr)
  = map (fun idocc => (GoIndex.mkKey (GoIndex.Snap.file_ref_path fr) (fst idocc), snd idocc))
        (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr)).
Proof.
  rewrite <- (GoIndex.Snap.visit_file_idocc p fr), map_map.
  apply map_ext_in. intros [r occ] Hin. cbn [fst snd].
  rewrite GoIndex.Snap.node_ref_key_eq.
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
Qed.

Lemma keyed_binding_visit (p : GoProgram) (b : FilePath * GoSourceFile) :
  In b (GoAST.file_bindings (prog_files p)) ->
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (binding_visit p b)
  = map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b)).
Proof.
  intro Hin. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hin) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, keyed_visit_file, Hpath, Hsrc. reflexivity.
Qed.

Definition keyed_visit (p : GoProgram) : list (GoIndex.NodeKey * GoIndex.SourceOccurrence) :=
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (prog_visit p).

Definition source_keyed_visit (fm : GoAST.GoFileMap) : list (GoIndex.NodeKey * GoIndex.SourceOccurrence) :=
  flat_map (fun b => map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b)))
           (GoAST.file_bindings fm).

Lemma keyed_visit_source (p : GoProgram) : keyed_visit p = source_keyed_visit (prog_files p).
Proof.
  unfold keyed_visit, source_keyed_visit. rewrite prog_visit_flat_map, map_flat_map.
  apply flat_map_ext_in. intros b Hin. exact (keyed_binding_visit p b Hin).
Qed.

(** §17 — the KEYED visit stream depends ONLY on the file map: [FilesEqual] programs have IDENTICAL keyed
    streams (their canonical [file_bindings] are the same list, and each file's [occs_file] is source-only). *)
Lemma keyed_visit_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> keyed_visit p1 = keyed_visit p2.
Proof.
  intro Heq. rewrite !keyed_visit_source. unfold source_keyed_visit.
  assert (Hb : GoAST.file_bindings (prog_files p1) = GoAST.file_bindings (prog_files p2)).
  { unfold GoAST.file_bindings. apply Collections.filemap_elements_Equal. exact Heq. }
  rewrite Hb. reflexivity.
Qed.

(* ---- §17 — the ONE-PASS enclosing context erases to a SOURCE function of the keyed stream.  [annotate_keyed]
   runs the SAME stack discipline over keyed entries (NodeKeys + occurrences), and the erased ref-annotation
   [annotate_encl] equals it.  So the erased [outer_context] depends only on the file map. ---- *)

(* the erasure of one annotated occurrence: its NodeKey, its occurrence, and its enclosing-context KEYS. *)
Definition erase_annot {p}
    (roc : (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p))
  : (GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey :=
  ((GoIndex.Snap.node_ref_key (fst (fst roc)), snd (fst roc)),
   map (fun er => GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (snd roc)).

Definition erase_estack {p} (stack : list (GoIndex.ExprRef p * positive)) : list (GoIndex.NodeKey * positive) :=
  map (fun e => (GoIndex.Snap.node_ref_key (GoIndex.erase_ref (fst e)), snd e)) stack.

Fixpoint annotate_keyed (stack : list (GoIndex.NodeKey * positive))
    (stream : list (GoIndex.NodeKey * GoIndex.SourceOccurrence))
    : list ((GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey) :=
  match stream with
  | [] => []
  | ke :: rest =>
      let open := filter (fun e => Pos.leb (GoIndex.nk_local (fst ke)) (snd e)) stack in
      let stack' := if is_conversion_occ (snd ke)
                    then (fst ke, GoIndex.occurrence_subtree_end (snd ke)) :: open else open in
      (ke, map fst open) :: annotate_keyed stack' rest
  end.

(* a conversion occurrence (on a VALID reference whose occurrence is its source) HAS an [ExprRef] erasing to it. *)
Lemma is_conversion_occ_as_expr {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) :
  is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref r) = true ->
  exists er, GoIndex.as_expr idx r = Some er /\ GoIndex.erase_ref er = r.
Proof.
  intro Hconv.
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx r). unfold is_conversion_occ in Hconv.
    destruct (GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref r)) as [e|] eqn:Ev;
      [ exact (GoIndex.view_expr_kind _ e Ev) | discriminate Hconv ]. }
  unfold GoIndex.as_expr. destruct (GoIndex.as_kind_complete idx r GoIndex.KExpression Hk) as [tr [Has Her]].
  exists tr; split; [exact Has | exact Her].
Qed.

Lemma map_filter_comm {A B} (f : A -> B) (g : B -> bool) (h : A -> bool) (l : list A) :
  (forall a, g (f a) = h a) -> map f (filter h l) = filter g (map f l).
Proof.
  intro Hgh. induction l as [|a l IH]; [reflexivity|]. cbn [filter map].
  rewrite <- Hgh. destruct (g (f a)); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma erase_estack_filter {p} (l : positive) (stack : list (GoIndex.ExprRef p * positive)) :
  erase_estack (filter (fun e => Pos.leb l (snd e)) stack)
  = filter (fun e => Pos.leb l (snd e)) (erase_estack stack).
Proof. unfold erase_estack. apply map_filter_comm. intro a. reflexivity. Qed.

(* THE SIMULATION: over a stream of VALID occurrences, the erased ref-annotation equals the keyed annotation. *)
Lemma annotate_encl_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) stack stream :
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  map erase_annot (annotate_encl idx stack stream)
  = annotate_keyed (erase_estack stack) (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) stream).
Proof.
  revert stack. induction stream as [|ro rest IH]; intro stack; intro Hval; [reflexivity|].
  pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
  cbn [annotate_encl map annotate_keyed fst snd].
  assert (Hok : filter (fun e => Pos.leb (GoIndex.nk_local (GoIndex.Snap.node_ref_key (fst ro))) (snd e))
                       (erase_estack stack)
              = erase_estack (filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro)) (snd e)) stack)).
  { rewrite erase_estack_filter, GoIndex.Snap.node_ref_key_eq. reflexivity. }
  f_equal.
  - unfold erase_annot. cbn [fst snd]. rewrite Hok. unfold erase_estack. rewrite !map_map. reflexivity.
  - rewrite (IH _ (fun ro' Hin => Hval ro' (or_intror Hin))), Hok. f_equal.
    destruct (is_conversion_occ (snd ro)) eqn:Hc.
    + assert (Hc' : is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (fst ro)) = true)
        by (rewrite <- Hsrc; exact Hc).
      destruct (is_conversion_occ_as_expr idx (fst ro) Hc') as [er [Ha He]].
      rewrite Ha. cbn [erase_estack map fst snd]. rewrite He.
      rewrite (GoIndex.Snap.node_subtree_end_matches_source p idx (fst ro)), <- Hsrc. reflexivity.
    + destruct (GoIndex.as_expr idx (fst ro)) as [er|]; reflexivity.
Qed.

(* each per-file visited occurrence IS its reference's exact source occurrence (the validity the simulation needs). *)
Lemma binding_visit_valid (p : GoProgram) (b : FilePath * GoSourceFile) :
  forall ro, In ro (binding_visit p b) -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro).
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Ho _]. exact Ho.
Qed.

(* the SOURCE enclosing-context annotation: per file, the keyed one-pass annotation over that file's source
   occurrence stream (keyed by the file's path).  A pure function of the file map. *)
Definition annotate_source (fm : GoAST.GoFileMap)
  : list ((GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey) :=
  flat_map (fun b => annotate_keyed []
              (map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b))))
           (GoAST.file_bindings fm).

Lemma annotate_program_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_annot (annotate_program idx) = annotate_source (prog_files p).
Proof.
  unfold annotate_program, prog_blocks. rewrite flat_map_map.
  unfold annotate_source. rewrite map_flat_map.
  apply flat_map_ext_in. intros b Hin.
  rewrite (annotate_encl_erased idx [] (binding_visit p b) (binding_visit_valid p b)).
  cbn [erase_estack]. f_equal. exact (keyed_binding_visit p b Hin).
Qed.

Lemma annotate_source_FilesEqual (fm1 fm2 : GoAST.GoFileMap) :
  GoAST.FilesEqual fm1 fm2 -> annotate_source fm1 = annotate_source fm2.
Proof.
  intro Heq. unfold annotate_source.
  assert (Hb : GoAST.file_bindings fm1 = GoAST.file_bindings fm2)
    by (unfold GoAST.file_bindings; apply Collections.filemap_elements_Equal; exact Heq).
  rewrite Hb. reflexivity.
Qed.


(* the ERASED expression diagnostic an annotated KEYED occurrence emits — the same decision as [occ_expr_diags]
   but over erased data (its NodeKey + occurrence + enclosing-context KEYS); a pure source function. *)
Definition erase_occ_diags (kroc : (GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey)
  : list ErasedDiagnostic :=
  match GoIndex.view_expr (snd (fst kroc)) with
  | None => []
  | Some e =>
      match local_conv_failure e with
      | Some (t, _) => [ mkErasedDiagnostic DCInvalidConversion (EANode (fst (fst kroc)))
                                            (map EANode (snd kroc)) (Some t) ]
      | None =>
          match arg_default_failure (snd (fst kroc)) e with
          | Some (_, dt) => [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (fst (fst kroc))) [] (Some dt) ]
          | None => []
          end
      end
  end.

(* erasing the two expression diagnostics, computed explicitly (isolating the anchor/target projection). *)
Lemma erase_diagnostic_invalid {p} (er : GoIndex.ExprRef p) outer t ci :
  erase_diagnostic (DRInvalidConversion er outer t ci)
  = mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)))
      (map (fun r => EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref r))) outer) (Some t).
Proof.
  unfold erase_diagnostic.
  cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erase_anchor].
  rewrite map_map. reflexivity.
Qed.

Lemma erase_diagnostic_default {p} (er : GoIndex.ExprRef p) c dt :
  erase_diagnostic (DRDefaultNotRepresentable er c dt)
  = mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er))) [] (Some dt).
Proof. reflexivity. Qed.

(* per VALID occurrence: erasing the ref-emitted diagnostics equals the keyed emitter on the erased annotation. *)
Lemma erase_occ_diags_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ ctx :
  occ = GoIndex.Snap.source_occurrence_of_ref r ->
  map erase_diagnostic (occ_expr_diags idx ctx (r, occ)) = erase_occ_diags (erase_annot ((r, occ), ctx)).
Proof.
  intro Hval. unfold occ_expr_diags, erase_occ_diags, erase_annot. cbn [fst snd].
  destruct (GoIndex.as_expr idx r) as [er|] eqn:Ea.
  - assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
    { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [He|]; [exact He|discriminate Ea]. }
    assert (Hke : GoIndex.occurrence_kind occ = GoIndex.KExpression)
      by (rewrite Hval, <- (GoIndex.Snap.node_kind_matches_source p idx r); exact Hk).
    destruct (GoIndex.kind_view_expr occ Hke) as [e Hv]. rewrite Hv.
    assert (Her : GoIndex.erase_ref er = r) by exact (GoIndex.erase_as_kind idx r GoIndex.KExpression er Ea).
    destruct (local_conv_failure e) as [[t ci]|].
    + cbn [map]. rewrite erase_diagnostic_invalid, Her, map_map. reflexivity.
    + destruct (arg_default_failure occ e) as [[c dt]|].
      * cbn [map]. rewrite erase_diagnostic_default, Her. reflexivity.
      * reflexivity.
  - assert (Hkne : GoIndex.Snap.node_kind idx r <> GoIndex.KExpression).
    { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression); [discriminate Ea|assumption]. }
    assert (Hvne : GoIndex.view_expr occ = None).
    { destruct (GoIndex.view_expr occ) as [e|] eqn:E; [|reflexivity]. exfalso. apply Hkne.
      rewrite (GoIndex.Snap.node_kind_matches_source p idx r), <- Hval. exact (GoIndex.view_expr_kind occ e E). }
    rewrite Hvne. reflexivity.
Qed.

(* the erased expression report over the annotated program = the keyed emitter over each occurrence. *)
Lemma erased_expr_diags_annot {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx)
  = flat_map (fun roc => erase_occ_diags (erase_annot roc)) (annotate_program idx).
Proof.
  rewrite expr_diags_eq_spec, map_flat_map. apply flat_map_ext_in.
  intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
  apply erase_occ_diags_eq.
  pose proof (in_map fst _ _ Hin) as Hin'. rewrite annotate_program_fst in Hin'. cbn [fst] in Hin'.
  exact (prog_visit_view p r occ Hin').
Qed.

(** §17 — the erased EXPRESSION report is a SOURCE function of the file map (via [annotate_source]). *)
Lemma erased_expr_diags_source {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx) = flat_map erase_occ_diags (annotate_source (prog_files p)).
Proof.
  rewrite erased_expr_diags_annot, <- (annotate_program_erased idx), flat_map_map. reflexivity.
Qed.

(* ---- §17 — the PACKAGE buckets erase to a SOURCE function of the keyed stream.  [keyed_ppkg_step] runs the
   SAME package-grouping over keyed entries (NodeKeys), and the erased ([node_ref_key . erase_ref]) buckets
   equal it (find-wise, hence PM.Equal).  So the erased package diagnostics depend only on the file map. ---- *)

Definition erase_dkey {p} (dr : GoIndex.DeclRef p) : GoIndex.NodeKey := GoIndex.Snap.node_ref_key (GoIndex.erase_ref dr).
Definition occ_pkg_key (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence) : string :=
  fp_parent (GoIndex.nk_file (fst ke)).

Definition keyed_ppkg_step (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence) (acc : PM.t (list GoIndex.NodeKey))
  : PM.t (list GoIndex.NodeKey) :=
  match GoIndex.occurrence_kind (snd ke) with
  | GoIndex.KTopLevelDecl =>
      PM.add (occ_pkg_key ke) (fst ke :: match PM.find (occ_pkg_key ke) acc with Some l => l | None => [] end) acc
  | GoIndex.KFile =>
      match PM.find (occ_pkg_key ke) acc with Some _ => acc | None => PM.add (occ_pkg_key ke) [] acc end
  | _ => acc
  end.

Definition keyed_buckets (l : list (GoIndex.NodeKey * GoIndex.SourceOccurrence)) : PM.t (list GoIndex.NodeKey) :=
  fold_right keyed_ppkg_step (PM.empty (list GoIndex.NodeKey)) l.

(* the keyed package of an occurrence equals its source parent directory (via [node_ref_key_eq]). *)
Lemma occ_pkg_key_eq {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :
  occ_pkg_key (GoIndex.Snap.node_ref_key (fst ro), snd ro) = occ_pkg ro.
Proof.
  unfold occ_pkg_key, occ_pkg. cbn [fst]. rewrite GoIndex.Snap.node_ref_key_eq. reflexivity.
Qed.

Lemma ppkg_erased_find {p} (idx : GoIndex.Snap.SyntaxIndex p) (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  (forall ro, In ro L -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  forall k, PM.find k (PM.map (map erase_dkey) (fold_right (ppkg_step idx) (PM.empty _) L))
          = PM.find k (keyed_buckets (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) L)).
Proof.
  induction L as [|ro L IH]; intro Hval.
  - intro k. rewrite PMF.map_o. cbn [fold_right map keyed_buckets]. rewrite !PMF.empty_o. reflexivity.
  - pose proof (IH (fun ro' Hin => Hval ro' (or_intror Hin))) as IHk.
    unfold keyed_buckets in IHk.
    pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
    assert (Hk : GoIndex.Snap.node_kind idx (fst ro) = GoIndex.occurrence_kind (snd ro))
      by (rewrite (GoIndex.Snap.node_kind_matches_source p idx (fst ro)), <- Hsrc; reflexivity).
    intro k. cbn [fold_right map keyed_buckets].
    set (acc := fold_right (ppkg_step idx) (PM.empty (list (GoIndex.DeclRef p))) L) in *.
    set (kacc := fold_right keyed_ppkg_step (PM.empty (list GoIndex.NodeKey))
                   (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) L)) in *.
    unfold ppkg_step at 1, keyed_ppkg_step at 1. cbn [fst snd]. rewrite occ_pkg_key_eq.
    destruct (GoIndex.occurrence_kind (snd ro)) eqn:Hok.
    + (* KFile: as_decl = None, as_kind KFile = Some — file-root init (presence, not length) *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      destruct (GoIndex.as_kind_complete idx (fst ro) GoIndex.KFile) as [fr [Hf _]]; [rewrite Hk; reflexivity|].
      rewrite Hd, Hf.
      pose proof (IHk (occ_pkg ro)) as IHo. rewrite PMF.map_o in IHo. rewrite <- IHo.
      destruct (PM.find (occ_pkg ro) acc) as [la|] eqn:Ea; cbn [option_map].
      * exact (IHk k).
      * destruct (String.eqb (occ_pkg ro) k) eqn:Ek.
        -- apply String.eqb_eq in Ek. rewrite PMF.map_o, PMF.add_eq_o, PMF.add_eq_o by exact Ek. reflexivity.
        -- apply String.eqb_neq in Ek. rewrite PMF.map_o, PMF.add_neq_o, PMF.add_neq_o by exact Ek.
           rewrite <- PMF.map_o. exact (IHk k).
    + (* KPackageClause: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* KTopLevelDecl: as_decl = Some dr — a main is prepended; its erased key IS the occurrence's key *)
      destruct (GoIndex.as_kind_complete idx (fst ro) GoIndex.KTopLevelDecl) as [dr [Hdr Her]];
        [ rewrite Hk; reflexivity | ].
      unfold GoIndex.as_decl. rewrite Hdr.
      pose proof (IHk (occ_pkg ro)) as IHo. rewrite PMF.map_o in IHo.
      destruct (String.eqb (occ_pkg ro) k) eqn:Ek.
      * apply String.eqb_eq in Ek. rewrite PMF.map_o, PMF.add_eq_o, PMF.add_eq_o by exact Ek.
        cbn [option_map map]. unfold erase_dkey. rewrite Her. f_equal. f_equal.
        rewrite <- IHo. destruct (PM.find (occ_pkg ro) acc) as [la|]; reflexivity.
      * apply String.eqb_neq in Ek. rewrite PMF.map_o, PMF.add_neq_o, PMF.add_neq_o by exact Ek.
        rewrite <- PMF.map_o. exact (IHk k).
    + (* KStatement: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* KExpression: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
Qed.

(* the erased buckets of the retained analysis EQUAL (find-wise, hence [PM.Equal]) the keyed source buckets. *)
Lemma prog_package_refs_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  PM.Equal (PM.map (map erase_dkey) (prog_package_refs idx)) (keyed_buckets (keyed_visit p)).
Proof.
  intro k. unfold prog_package_refs, keyed_visit.
  apply (ppkg_erased_find idx (prog_visit p)).
  intros [r occ] Hin. exact (prog_visit_view p r occ Hin).
Qed.

(* the ERASED package diagnostics of one bucket, over its erased (NodeKey) keys — a pure source function. *)
Definition erase_bucket_diag (kv : string * list GoIndex.NodeKey) : list ErasedDiagnostic :=
  match snd kv with
  | nil        => [ mkErasedDiagnostic DCMissingMain (EAPackage (fst kv)) [] None ]
  | e1 :: erest => map (fun ek => mkErasedDiagnostic DCDuplicateMain (EANode ek) [EANode e1] None) erest
  end.

Lemma pkg_diag_of_bucket_erased {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt :
  map erase_diagnostic (@pkg_diag_of_bucket p m Hpres dir l Hmt)
  = erase_bucket_diag (dir, map erase_dkey l).
Proof.
  unfold pkg_diag_of_bucket, erase_bucket_diag. cbn [snd]. destruct l as [|d1 rest]; cbn [map].
  - unfold erase_diagnostic. cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erase_anchor].
    reflexivity.
  - rewrite !map_map. unfold erase_diagnostic, erase_dkey.
    cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erase_anchor map]. reflexivity.
Qed.

Lemma bucket_diags_elems_erased {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall :
  map erase_diagnostic (@bucket_diags_elems p m Hpres es Hall)
  = flat_map erase_bucket_diag (map (fun kv => (fst kv, map erase_dkey (snd kv))) es).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems map flat_map]; [reflexivity|].
  rewrite map_app, IH. f_equal. apply pkg_diag_of_bucket_erased.
Qed.

(** §17 — the erased PACKAGE report is a SOURCE function of the file map (via the keyed source buckets). *)
Lemma erased_pkg_diags_source {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (pkg_diags idx)
  = flat_map erase_bucket_diag (PM.elements (keyed_buckets (keyed_visit p))).
Proof.
  unfold pkg_diags. rewrite bucket_diags_elems_erased.
  rewrite <- Collections.packagemap_map_elements.
  rewrite (Collections.packagemap_elements_Equal _ _ (prog_package_refs_erased idx)). reflexivity.
Qed.

Lemma erased_pkg_diags_FilesEqual (p1 p2 : GoProgram)
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  map erase_diagnostic (pkg_diags idx1) = map erase_diagnostic (pkg_diags idx2).
Proof.
  intro Heq. rewrite !erased_pkg_diags_source, (keyed_visit_FilesEqual p1 p2 Heq). reflexivity.
Qed.

(** the WHOLE erased report as a PURE SOURCE function of the file map — expression diagnostics via
    [annotate_source] (occurrence keys + open-conversion context) then package diagnostics via the keyed source
    buckets.  Since it mentions no [Snap] projection it [vm_compute]s to the exact [ErasedDiagnostic] list (code
    + NodeKey/package anchors + target payload) for any concrete program — the basis of the EXACT §22 fixtures. *)
(* the ERASED node-diagnostic key/code/partition (mirroring the dependent ones, over snapshot-free anchors). *)
Definition ecode (e : ErasedDiagnostic) : nat := diagnostic_code_index (ed_code e).
Definition enode_key (e : ErasedDiagnostic) : option GoIndex.NodeKey :=
  match ed_primary e with EANode k => Some k | _ => None end.
Definition enode_keyed (l : list ErasedDiagnostic) : list (GoIndex.NodeKey * ErasedDiagnostic) :=
  flat_map (fun e => match enode_key e with Some k => [(k, e)] | None => [] end) l.
Definition epkg_primary (l : list ErasedDiagnostic) : list ErasedDiagnostic :=
  flat_map (fun e => match enode_key e with Some _ => [] | None => [e] end) l.

(* the raw (unordered) erased source diagnostics — expression scars over [annotate_source], then the keyed
   source package buckets. *)
Definition erased_src_diags (fm : GoAST.GoFileMap) : list ErasedDiagnostic :=
  flat_map erase_occ_diags (annotate_source fm)
  ++ flat_map erase_bucket_diag (PM.elements (keyed_buckets (source_keyed_visit fm))).

(** the WHOLE erased report as a PURE SOURCE function of the file map, in §16 canonical order: node-primary
    diagnostics bucketed by NodeKey and flattened in path/local order (code-ordered inside a bucket), THEN the
    package-primary (missing-main) diagnostics.  It mentions no [Snap] projection, so it [vm_compute]s to the
    exact ordered [ErasedDiagnostic] list — the basis of the EXACT §22 fixtures. *)
Definition erased_report_src (fm : GoAST.GoFileMap) : list ErasedDiagnostic :=
  bucket_flatten ecode (enode_keyed (erased_src_diags fm)) ++ epkg_primary (erased_src_diags fm).

Lemma ecode_erase {p} (d : DiagnosticReason p) : ecode (erase_diagnostic d) = dcode d.
Proof. reflexivity. Qed.

Lemma enode_key_erase {p} (d : DiagnosticReason p) : enode_key (erase_diagnostic d) = diag_node_key d.
Proof. destruct d; reflexivity. Qed.

Lemma node_keyed_erase {p} (l : list (DiagnosticReason p)) :
  map (fun kd => (fst kd, erase_diagnostic (snd kd))) (node_keyed l) = enode_keyed (map erase_diagnostic l).
Proof.
  induction l as [|d rest IH]; [reflexivity|].
  replace (node_keyed (d :: rest))
    with ((match diag_node_key d with Some k => [(k, d)] | None => nil end) ++ node_keyed rest) by reflexivity.
  replace (enode_keyed (map erase_diagnostic (d :: rest)))
    with ((match enode_key (erase_diagnostic d) with Some k => [(k, erase_diagnostic d)] | None => nil end)
          ++ enode_keyed (map erase_diagnostic rest)) by reflexivity.
  rewrite map_app, IH, enode_key_erase. destruct (diag_node_key d) as [k|]; reflexivity.
Qed.

Lemma pkg_primary_erase {p} (l : list (DiagnosticReason p)) :
  map erase_diagnostic (pkg_primary l) = epkg_primary (map erase_diagnostic l).
Proof.
  induction l as [|d rest IH]; [reflexivity|].
  replace (pkg_primary (d :: rest))
    with ((match diag_node_key d with Some _ => nil | None => [d] end) ++ pkg_primary rest) by reflexivity.
  replace (epkg_primary (map erase_diagnostic (d :: rest)))
    with ((match enode_key (erase_diagnostic d) with Some _ => nil | None => [erase_diagnostic d] end)
          ++ epkg_primary (map erase_diagnostic rest)) by reflexivity.
  rewrite map_app, IH, enode_key_erase. destruct (diag_node_key d) as [k|]; reflexivity.
Qed.

Lemma erased_src_diags_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx ++ pkg_diags idx) = erased_src_diags (prog_files p).
Proof.
  unfold erased_src_diags. rewrite map_app, erased_expr_diags_source, erased_pkg_diags_source, keyed_visit_source.
  reflexivity.
Qed.

Lemma erased_report_src_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  erased_report p idx = erased_report_src (prog_files p).
Proof.
  unfold erased_report, erased_report_src, collect_diagnostics. rewrite map_app. f_equal.
  - rewrite (bucket_flatten_map erase_diagnostic dcode ecode (@ecode_erase p)
              (node_keyed (expr_diags idx ++ pkg_diags idx))).
    rewrite node_keyed_erase, erased_src_diags_eq. reflexivity.
  - rewrite pkg_primary_erase, erased_src_diags_eq. reflexivity.
Qed.

Lemma erased_src_diags_FilesEqual (fm1 fm2 : GoAST.GoFileMap) :
  GoAST.FilesEqual fm1 fm2 -> erased_src_diags fm1 = erased_src_diags fm2.
Proof.
  intro Heq. unfold erased_src_diags. rewrite (annotate_source_FilesEqual _ _ Heq). f_equal.
  assert (Hb : GoAST.file_bindings fm1 = GoAST.file_bindings fm2)
    by (unfold GoAST.file_bindings; apply Collections.filemap_elements_Equal; exact Heq).
  unfold source_keyed_visit. rewrite Hb. reflexivity.
Qed.

(** §17 (C3 FINAL) — THE cross-snapshot determinism theorem: two programs with the SAME file map (their
    diagnostics live in DIFFERENT dependent snapshot types) produce the IDENTICAL erased report — it depends
    ONLY on the file map (the erased report is [erased_report_src (prog_files p)], a source function). *)
Theorem erased_report_FilesEqual (p1 p2 : GoProgram)
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intro Heq. rewrite !erased_report_src_eq. unfold erased_report_src.
  rewrite (erased_src_diags_FilesEqual _ _ Heq). reflexivity.
Qed.

(** §17 (C3 FINAL) — CONSTRUCTION-list permutation corollary: building the SAME module from a PERMUTED file-node
    list yields the IDENTICAL erased report (permuted nodes build the same [FilesEqual] map — the standard
    duplicate-rejecting [filemap_of_nodes] is order-independent — so the report, a function of the map, is
    unchanged).  The report is invariant to the order in which the proposer supplies the files. *)
Theorem erased_report_build_permutation : forall ms nodes1 nodes2 p1 p2
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2),
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intros ms nodes1 nodes2 p1 p2 idx1 idx2 Hperm Hb1 Hb2.
  apply erased_report_FilesEqual. unfold build_program in *.
  destruct (filemap_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(* ---- §17/§20/§27 — SUCCESSFUL-fact enumeration determinism.  The expression fact table's keys are SOURCE
   NodeKeys and its values source-derived, so it is a fold-map fusion over the keyed stream — a pure source
   function of the file map, needing no erasure. ---- *)
Definition keyed_add (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) : GoIndex.NodeKeyMapBase.t ExprFact :=
  match occ_expr_fact (snd ke) with
  | Some f => GoIndex.NodeKeyMapBase.add (fst ke) f m
  | None => m
  end.

Definition keyed_facts (l : list (GoIndex.NodeKey * GoIndex.SourceOccurrence)) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right keyed_add (GoIndex.NodeKeyMapBase.empty ExprFact) l.

Lemma prog_expr_facts_source (p : GoProgram) : prog_expr_facts p = keyed_facts (keyed_visit p).
Proof.
  rewrite prog_expr_facts_eq_spec. unfold keyed_facts, keyed_visit.
  induction (prog_visit p) as [|ro L IH]; [reflexivity|].
  cbn [map fold_right]. rewrite IH. unfold add_occ_fact, keyed_add. cbn [fst snd]. reflexivity.
Qed.

(** §17/§20/§27 (C3 FINAL) — SUCCESSFUL-fact enumeration determinism: the expression fact table (each visited
    occurrence's key -> its exact ConstInfo + println-use fact) depends ONLY on the file map — its keys are
    source NodeKeys and its values source-derived (a fold-map fusion over the keyed stream) — so FilesEqual
    programs have the IDENTICAL fact table, hence the IDENTICAL canonical fact enumeration. *)
Lemma prog_expr_facts_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> prog_expr_facts p1 = prog_expr_facts p2.
Proof.
  intro Heq. rewrite !prog_expr_facts_source, (keyed_visit_FilesEqual p1 p2 Heq). reflexivity.
Qed.

Theorem prog_expr_facts_enum_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  GoIndex.NodeKeyMapBase.elements (prog_expr_facts p1) = GoIndex.NodeKeyMapBase.elements (prog_expr_facts p2).
Proof. intro Heq. rewrite (prog_expr_facts_FilesEqual p1 p2 Heq). reflexivity. Qed.

(* ---- the TWO disjoint diagnostic families (typing / package), used to PROJECT a legacy compile class from
   the diagnostics (never a second check).  Expression diagnostics are typing-class; package diagnostics are
   package-class; the two are disjoint. ---- *)

Definition diag_is_typing {p} (d : DiagnosticReason p) : bool :=
  match diagnostic_code d with DCInvalidConversion | DCDefaultNotRepresentable => true | _ => false end.
Definition diag_is_package {p} (d : DiagnosticReason p) : bool :=
  match diagnostic_code d with DCDuplicateMain | DCMissingMain => true | _ => false end.

Lemma existsb_all_true {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = true) -> existsb f l = match l with [] => false | _ => true end.
Proof. destruct l as [|x xs]; [reflexivity|]. intro H. cbn [existsb]. rewrite (H x (or_introl eq_refl)). reflexivity. Qed.

Lemma existsb_all_false {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  induction l as [|x xs IH]; [reflexivity|]. intro H. cbn [existsb].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma occ_expr_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro : forall d,
  In d (occ_expr_diags idx outer ro) -> diag_is_typing d = true /\ diag_is_package d = false.
Proof.
  intros d Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er|]; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|]; [| destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct Hin as [<-|[]]. split; reflexivity.
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [ destruct Hin as [<-|[]]; split; reflexivity | destruct Hin ].
Qed.

Lemma expr_diags_typing {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (expr_diags idx) -> diag_is_typing d = true.
Proof.
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [roc [_ Hd]].
  apply (occ_expr_diags_family idx (snd roc) (fst roc) d Hd).
Qed.
Lemma expr_diags_not_package {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (expr_diags idx) -> diag_is_package d = false.
Proof.
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [roc [_ Hd]].
  apply (occ_expr_diags_family idx (snd roc) (fst roc) d Hd).
Qed.

Lemma pkg_diag_of_bucket_family {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt : forall d,
  In d (@pkg_diag_of_bucket p m Hpres dir l Hmt) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  intros d Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [<-|[]]; split; reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [dk [<- _]]. split; reflexivity.
Qed.

Lemma bucket_diags_elems_family {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall : forall d,
  In d (@bucket_diags_elems p m Hpres es Hall) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems]; intros d Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exact (pkg_diag_of_bucket_family m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl)) d Hin).
    + exact (IH (fun kv' Hin' => Hall kv' (or_intror Hin')) d Hin).
Qed.

Lemma pkg_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d,
  In d (pkg_diags idx) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  intros d Hin. unfold pkg_diags in Hin. exact (bucket_diags_elems_family _ _ _ _ d Hin).
Qed.

(** §9 (C3 FINAL) — code-specific PACKAGE-diagnostic soundness.  A [DRMissingMain] comes from an EMPTY bucket
    and anchors at THAT package key (the [PackageRef] carries its own presence proof — [package_ref_ok] — so
    the package is represented in [p]); an empty bucket length is the package's zero [main] count
    ([prog_package_refs_bucket_len]), i.e. there is genuinely no [DMain]. *)
Lemma pkg_diag_of_bucket_missing_sound {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt pk :
  In (DRMissingMain pk) (@pkg_diag_of_bucket p m Hpres dir l Hmt) ->
  l = nil /\ package_ref_key pk = dir.
Proof.
  intro Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. injection Heq as Hpk. subst pk. split; reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq _]]. discriminate Heq.
Qed.

(** A [DRDuplicateMain later earlier] comes from a bucket [earlier :: rest] with [later] in the TAIL: the
    related [earlier] is the FIRST canonical main and the primary [later] is a strictly-later main in the same
    bucket (hence same package — [prog_package_refs_belongs] — and in canonical bucket order). *)
Lemma pkg_diag_of_bucket_dup_sound {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt later earlier :
  In (DRDuplicateMain later earlier) (@pkg_diag_of_bucket p m Hpres dir l Hmt) ->
  exists rest, l = earlier :: rest /\ In later rest.
Proof.
  intro Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. discriminate Heq.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq Hdk]]. injection Heq as Hl He.
    exists rest. split; [ rewrite <- He; reflexivity | rewrite <- Hl; exact Hdk ].
Qed.

(* a diagnostic in the flattened bucket enumeration comes from SOME mapped bucket of [m]. *)
Lemma bucket_diags_elems_in {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall : forall d,
  In d (@bucket_diags_elems p m Hpres es Hall) ->
  exists dir l (Hmt : PM.MapsTo dir l m), In d (@pkg_diag_of_bucket p m Hpres dir l Hmt).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems]; intros d Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exists (fst kv), (snd kv), (Hall kv (or_introl eq_refl)). exact Hin.
    + destruct (IH (fun kv' Hin' => Hall kv' (or_intror Hin')) d Hin) as [dir [l [Hmt Hd]]].
      exists dir, l, Hmt. exact Hd.
Qed.

(** §9 (C3 FINAL) — the WHOLE-program [DRDuplicateMain] soundness DENOTES its code: the primary [later] and the
    related [earlier] both anchor genuine TOP-LEVEL declarations (the only [GoDecl] is [DMain] — `func main`),
    they lie in the SAME package (equal parent directory — [prog_package_refs_belongs]), and [earlier] is the
    FIRST canonical main of that package's bucket with [later] a strictly-later one. *)
Lemma pkg_diags_dup_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) later earlier :
  In (DRDuplicateMain later earlier) (pkg_diags idx) ->
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref later)))
    = fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref earlier)))
  /\ GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref later)) = GoIndex.KTopLevelDecl
  /\ GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref earlier)) = GoIndex.KTopLevelDecl.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PM.find dir (prog_package_refs idx) = Some l) by (apply PM.find_1; exact Hmt).
  assert (HinE : In earlier l) by (rewrite Hl; left; reflexivity).
  assert (HinL : In later l)  by (rewrite Hl; right; exact Hlater).
  split; [ | split ].
  - rewrite (prog_package_refs_belongs idx dir l Hfind later HinL),
            (prog_package_refs_belongs idx dir l Hfind earlier HinE); reflexivity.
  - exact (GoIndex.noderefof_kind later).
  - exact (GoIndex.noderefof_kind earlier).
Qed.

(** §9 (C3 FINAL) — the WHOLE-program [DRMissingMain] soundness: a missing-main diagnostic anchors a package
    that IS represented in the program ([package_ref_ok]) and genuinely contains ZERO [DMain] declarations (its
    exact [pkg_main_count] is 0 — the empty bucket's length). *)
Lemma pkg_diags_missing_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) pk :
  In (DRMissingMain pk) (pkg_diags idx) ->
  package_present_b p (package_ref_key pk) = true
  /\ pkg_main_count (package_ref_key pk) (prog_files p) = 0%nat.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_missing_sound _ _ dir l Hmt pk Hd) as [Hl Hkey]. subst l.
  split.
  - exact (package_ref_ok pk).
  - rewrite Hkey. symmetry. exact (prog_package_refs_bucket_len idx dir nil (PM.find_1 Hmt)).
Qed.

(* ---- §9 — the package buckets are NodeKey-SORTED and DUPLICATE-FREE, hence duplicate-main diagnostics carry
   strict canonical precedence + distinctness.  Foundation: the whole visit stream is NodeKey-sorted. ---- *)

(* one file's block is NodeKey-sorted: same file (path constant), local strictly ascending. *)
Lemma visit_file_key_sorted {p} (fr : GoIndex.Snap.FileRef p) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (GoIndex.Snap.visit_file fr).
Proof.
  apply (StronglySorted_impl_in (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y)))).
  - intros [rx ox] [ry oy] Hx Hy Hlt.
    destruct (GoIndex.Snap.visit_file_view p fr rx ox Hx) as [_ Hfx].
    destruct (GoIndex.Snap.visit_file_view p fr ry oy Hy) as [_ Hfy].
    cbn [fst] in *. rewrite (GoIndex.Snap.node_ref_key_eq rx), (GoIndex.Snap.node_ref_key_eq ry).
    right. cbn [GoIndex.nk_file GoIndex.nk_local]. split; [ rewrite Hfx, Hfy; reflexivity | exact Hlt ].
  - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
Qed.

(* every node visited in binding [b]'s block has that binding's path as its key's file component. *)
Lemma binding_block_key_file (p : GoProgram) (b : FilePath * GoSourceFile) :
  forall ro, In ro (binding_visit p b) -> GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst ro)) = fst b.
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf].
  cbn [fst]. rewrite (GoIndex.Snap.node_ref_key_eq r). cbn [GoIndex.nk_file]. rewrite Hf.
  exact (GoIndex.Snap.file_of_path_sound p (fst b) fr Efr).
Qed.

Lemma prog_visit_key_sorted_aux (p : GoProgram) (L : list (FilePath * GoSourceFile)) :
  StronglySorted (fun a b => Collections.FilePath_OT.lt (fst a) (fst b)) L ->
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (concat (map (binding_visit p) L)).
Proof.
  induction L as [|b L IH]; intro Hbsort; [constructor|].
  apply StronglySorted_inv in Hbsort. destruct Hbsort as [Hbs Hbhd].
  cbn [map concat]. apply StronglySorted_app.
  { unfold binding_visit. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [apply visit_file_key_sorted | constructor]. }
  { apply IH; exact Hbs. }
  intros x y Hx Hy. apply in_concat in Hy. destruct Hy as [block [Hblock Hyb]].
  apply in_map_iff in Hblock. destruct Hblock as [b' [Hb'v Hb'L]]. subst block.
  assert (Hxf : GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst x)) = fst b) by (apply binding_block_key_file; exact Hx).
  assert (Hyf : GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst y)) = fst b') by (apply binding_block_key_file; exact Hyb).
  rewrite Forall_forall in Hbhd. pose proof (Hbhd b' Hb'L) as Hlt.
  unfold GoIndex.NodeKey_OT.lt. left. rewrite Hxf, Hyf. exact Hlt.
Qed.

Lemma prog_visit_key_sorted (p : GoProgram) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (prog_visit p).
Proof.
  unfold prog_visit, prog_blocks. apply prog_visit_key_sorted_aux.
  apply Sorted_StronglySorted; [ intros x y z; apply Collections.FilePath_OT.lt_trans | ].
  unfold GoAST.file_bindings. apply Collections.FileMapBase.elements_3.
Qed.

(* one [ppkg_step]'s effect on ONE package bucket, as an actual list: it prepends this occurrence's DeclRef
   (when it mints one for THIS package), else leaves the bucket unchanged.  (A file-root init adds an empty
   bucket — presence, not a list element.)  Mirrors [ppkg_step_olen] at the list level. *)
Lemma ppkg_step_bucket {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  (match PM.find dir (ppkg_step idx ro acc) with Some bk => bk | None => nil end)
  = (if String.eqb (occ_pkg ro) dir
     then match GoIndex.as_decl idx (fst ro) with
          | Some dr => dr :: (match PM.find dir acc with Some bk => bk | None => nil end)
          | None => (match PM.find dir acc with Some bk => bk | None => nil end)
          end
     else (match PM.find dir acc with Some bk => bk | None => nil end)).
Proof.
  unfold ppkg_step. destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l0|] eqn:Efind.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; subst dir | ]; reflexivity.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity.
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Definition bucket_of {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (dir : string) : list (GoIndex.DeclRef p) :=
  match PM.find dir (fold_right (ppkg_step idx) (PM.empty _) l) with Some bk => bk | None => nil end.

(* the fold's action on the head occurrence, stated over [bucket_of] (a real head symbol, so [rewrite]'s keyed
   unification finds it — a bare [match] LHS has no head to key on). *)
Lemma ppkg_fold_bucket_cons {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (dir : string) :
  bucket_of idx (ro :: l) dir
  = (if String.eqb (occ_pkg ro) dir
     then match GoIndex.as_decl idx (fst ro) with
          | Some dr => dr :: bucket_of idx l dir
          | None => bucket_of idx l dir
          end
     else bucket_of idx l dir).
Proof. unfold bucket_of. cbn [fold_right]. apply (ppkg_step_bucket idx ro (fold_right (ppkg_step idx) (PM.empty _) l) dir). Qed.

(* over a NodeKey-sorted stream, every package bucket is NodeKey-sorted, and each ref erases to an occurrence
   in the stream (so its key is one of the stream's keys — used to establish the strict prepend order). *)
Lemma ppkg_dir_sorted {p} (idx : GoIndex.Snap.SyntaxIndex p) (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y))) l ->
  forall dir,
    StronglySorted (fun a b => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (GoIndex.erase_ref a))
                                                     (GoIndex.Snap.node_ref_key (GoIndex.erase_ref b))) (bucket_of idx l dir)
    /\ (forall a, In a (bucket_of idx l dir) -> exists ro, In ro l /\ GoIndex.erase_ref a = fst ro).
Proof.
  induction l as [|ro l IH]; intro Hsort; intro dir.
  - unfold bucket_of. rewrite PMF.empty_o. split; [constructor | intros a []].
  - apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
    specialize (IH Hsort0). destruct (IH dir) as [IHsort IHref]. split.
    + (* the bucket stays NodeKey-sorted *)
      rewrite (ppkg_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occ_pkg ro) dir) eqn:Ek; [ destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed | ]; try exact IHsort.
      (* prepend this file's main ref — smaller key than every later main (stream sorted) *)
      assert (Her : GoIndex.erase_ref dr = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl dr Ed).
      constructor; [ exact IHsort |].
      rewrite Forall_forall. intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]].
      rewrite Forall_forall in Hhd. rewrite Her, Hae. exact (Hhd ro' Hro').
    + (* every bucket ref erases to a stream occurrence *)
      rewrite (ppkg_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occ_pkg ro) dir) eqn:Ek; [ destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed | ].
      * assert (Her : GoIndex.erase_ref dr = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl dr Ed).
        intros a [Hah | Hat].
        -- subst a. exists ro. split; [left; reflexivity | exact Her].
        -- destruct (IHref a Hat) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
Qed.
(** §9 (C3 FINAL) — the WHOLE-program [DRDuplicateMain] PRECEDENCE + DISTINCTNESS: because every package bucket
    is the strictly-NodeKey-ascending subselection of the sorted visit stream ([ppkg_dir_sorted] over
    [prog_visit_key_sorted]), the related [earlier] main is strictly BEFORE the primary [later] in canonical
    occurrence order, and the two are DISTINCT.  So the canonical main a package keeps is unambiguous — the
    unique smallest-key one — and every duplicate diagnostic names a genuinely different, strictly-later main. *)
Lemma pkg_diags_dup_precedence {p} (idx : GoIndex.Snap.SyntaxIndex p) later earlier :
  In (DRDuplicateMain later earlier) (pkg_diags idx) ->
  GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier))
                        (GoIndex.Snap.node_ref_key (GoIndex.erase_ref later))
  /\ earlier <> later.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PM.find dir (prog_package_refs idx) = Some l) by (apply PM.find_1; exact Hmt).
  assert (Hbeq : bucket_of idx (prog_visit p) dir = l).
  { unfold bucket_of. unfold prog_package_refs in Hfind. rewrite Hfind. reflexivity. }
  destruct (ppkg_dir_sorted idx (prog_visit p) (prog_visit_key_sorted p) dir) as [Hsort _].
  rewrite Hbeq, Hl in Hsort. apply StronglySorted_inv in Hsort. destruct Hsort as [_ Hhd].
  rewrite Forall_forall in Hhd. pose proof (Hhd later Hlater) as Hlt.
  split; [ exact Hlt |].
  intro Heq. subst later.
  assert (Hne : ~ GoIndex.NodeKey_OT.eq (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier))
                                        (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier)))
    by (apply GoIndex.NodeKey_OT.lt_not_eq; exact Hlt).
  apply Hne. apply (proj2 (GoIndex.nodekey_compare_eq _ _)). reflexivity.
Qed.

Lemma pkg_diags_package {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (pkg_diags idx) -> diag_is_package d = true.
Proof. intros d Hin; apply (pkg_diags_family idx d Hin). Qed.
Lemma pkg_diags_not_typing {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (pkg_diags idx) -> diag_is_typing d = false.
Proof. intros d Hin; apply (pkg_diags_family idx d Hin). Qed.

(** the diagnostic-derived TYPING flag is exactly "not program-typed"; the PACKAGE flag (when typed) is exactly
    "not one-main-per-package".  So the legacy class is a PROJECTION of the diagnostics, matching the decision. *)
Lemma existsb_typing_collect (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  existsb diag_is_typing (collect_diagnostics p idx) = negb (program_typedb p).
Proof.
  rewrite (existsb_In_eq _ _ _ (collect_diagnostics_In idx)), existsb_app.
  rewrite (existsb_all_false diag_is_typing (pkg_diags idx) (pkg_diags_not_typing idx)), Bool.orb_false_r.
  rewrite (existsb_all_true diag_is_typing (expr_diags idx) (expr_diags_typing idx)).
  destruct (expr_diags idx) as [|d ds] eqn:E.
  - rewrite (proj1 (expr_diags_empty_iff idx) E). reflexivity.
  - destruct (program_typedb p) eqn:Ht; [ | reflexivity ].
    exfalso. pose proof (proj2 (expr_diags_empty_iff idx) Ht) as Hc. rewrite Hc in E; discriminate E.
Qed.
Lemma existsb_package_collect (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  existsb diag_is_package (collect_diagnostics p idx) = negb (pkg_all_ok p).
Proof.
  rewrite (existsb_In_eq _ _ _ (collect_diagnostics_In idx)), existsb_app.
  rewrite (existsb_all_false diag_is_package (expr_diags idx) (expr_diags_not_package idx)), Bool.orb_false_l.
  rewrite (existsb_all_true diag_is_package (pkg_diags idx) (pkg_diags_package idx)).
  destruct (pkg_diags idx) as [|d ds] eqn:E.
  - rewrite (proj1 (pkg_diags_empty_iff idx) E). reflexivity.
  - destruct (pkg_all_ok p) eqn:Ht; [ | reflexivity ].
    exfalso. pose proof (proj2 (pkg_diags_empty_iff idx) Ht) as Hc. rewrite Hc in E; discriminate E.
Qed.

(** §12 (C3) — the SUCCESSFUL analysis facts, retained over the SAME [IndexedProgram] the analysis ran on:
    the occurrence-keyed [ExprFactTable] (standard NodeKey map) + the package main-ref buckets (standard
    PackageMap), each with its EXACTNESS proof, plus the compiled validity.  Facts are exposed ONLY on
    success. *)
Record CompilationFacts (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type := mkCompilationFacts {
  (* the SEALED expression-fact table: no non-expression/foreign key, each visited occurrence's fact exact. *)
  cf_expr_facts      : ExprFactTable p ip ;
  cf_package_refs    : PM.t (list (GoIndex.DeclRef p)) ;
  (* the bucket map's domain is exactly the represented package set... *)
  cf_package_present : forall dir, PM.In dir cf_package_refs <-> list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true ;
  (* ...each present bucket's length is the package's declarative main count... *)
  cf_package_len     : forall dir l, PM.find dir cf_package_refs = Some l -> length l = pkg_main_count dir (prog_files p) ;
  (* ...and every main in a bucket BELONGS to that package (its file's parent = the key) — no swap between packages. *)
  cf_package_belongs : forall dir l, PM.find dir cf_package_refs = Some l ->
                         forall d, In d l ->
                         fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref d))) = dir ;
  cf_valid           : ProgValid p
}.
Arguments mkCompilationFacts {p ip} _ _ _ _ _ _.
Arguments cf_expr_facts {p ip} _.
Arguments cf_package_refs {p ip} _.
Arguments cf_package_present {p ip} _.
Arguments cf_package_len {p ip} _.
Arguments cf_package_belongs {p ip} _.
Arguments cf_valid {p ip} _.

(** §10/§27 — the public expression-fact query is TOTAL: on a valid [CompilationFacts], EVERY typed [ExprRef]
    has an exact entry.  The ExprRef denotes a VISITED expression occurrence ([noderef_in_prog_visit] +
    [kind_view_expr]) whose [const_info] SUCCEEDS on a [ProgramTyped] program ([prog_visit_const_info_some],
    from [cf_valid]); [eft_complete] equates the map lookup to that occurrence's [occ_expr_fact], which is
    therefore [Some].  So the lookup is never [None] — the query returns an [ExprFact], not an option. *)
Lemma expr_ref_fact_some {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) :
  exists f, GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er))
              (eft_map (cf_expr_facts facts)) = Some f.
Proof.
  assert (Hkind : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = GoIndex.KExpression)
    by exact (proj2_sig er).
  destruct (GoIndex.kind_view_expr _ Hkind) as [e' Hv].
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref er)) as Hin.
  pose proof (proj2 (GoTypes.program_typedb_iff p) (proj1 (cf_valid facts))) as HPT.
  destruct (prog_visit_const_info_some p HPT (GoIndex.erase_ref er)
              (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) e' Hin Hv) as [ci Hci].
  pose proof (eft_complete (cf_expr_facts facts) (GoIndex.erase_ref er)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) Hin) as Hfind.
  exists (mkExprFact ci (occ_use_resolved (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)))).
  rewrite Hfind. exact (occ_expr_fact_status _ e' ci Hv Hci).
Qed.

Lemma expr_fact_at_not_none {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)) = None -> False.
Proof. intro Hn. destruct (expr_ref_fact_some facts er) as [f Hf]. rewrite Hf in Hn; discriminate. Qed.

(* the option-free lookup: a genuine match on the (variable) lookup result, discharging [None] by the totality
   proof — so a defect-shipping [option] result is impossible. *)
Definition fact_of_find {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p)
  (o : option ExprFact) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)) = o -> ExprFact :=
  match o with
  | Some f => fun _ => f
  | None   => fun Hn => False_rect ExprFact (expr_fact_at_not_none facts er Hn)
  end.

Definition expr_fact_at {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) : ExprFact :=
  fact_of_find facts er
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)))
    eq_refl.

Lemma fact_of_find_some {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) o Ho f :
  o = Some f -> fact_of_find facts er o Ho = f.
Proof. intros ->. cbn. reflexivity. Qed.

(** the total query PROJECTS the underlying map: where the map holds a fact, [expr_fact_at] returns exactly it
    (so the total function is faithful to the sealed table, not a fresh value). *)
Lemma expr_fact_at_find {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) f :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)) = Some f ->
  expr_fact_at facts er = f.
Proof.
  intro Hf. unfold expr_fact_at.
  exact (fact_of_find_some facts er
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)))
    eq_refl f Hf).
Qed.

(** on SUCCESS each package's bucket is a singleton (length = main count = 1). *)
Lemma cf_package_singleton {p ip} (facts : CompilationFacts p ip) dir l :
  PM.find dir (cf_package_refs facts) = Some l -> exists d, l = [d].
Proof.
  intro E. pose proof (cf_package_len facts dir l E) as Hlen.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { apply (cf_package_present facts dir). apply PMF.in_find_iff. rewrite E. discriminate. }
  assert (Hmt : PM.MapsTo dir (mkPkgSummary (pkg_main_count dir (prog_files p))) (package_summaries (prog_files p))).
  { apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (proj2 (cf_valid facts) dir _ Hmt) as Hone. cbn [ps_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(** the public package-main query, TOTAL on success: the package's ONE canonical main, a PROJECTION of the
    retained facts (the singleton bucket's head) — never recomputed from a separate index. *)
Definition package_main_at {p ip} (facts : CompilationFacts p ip) (r : PackageRef p) : GoIndex.DeclRef p.
Proof.
  remember (PM.find (package_ref_key r) (cf_package_refs facts)) as o eqn:E.
  destruct o as [l|].
  - destruct l as [|d rest].
    + exfalso. destruct (cf_package_singleton facts (package_ref_key r) [] (eq_sym E)) as [d Hd]; discriminate Hd.
    + exact d.
  - exfalso.
    assert (Hin : PM.In (package_ref_key r) (cf_package_refs facts))
      by (apply (cf_package_present facts), (package_ref_ok r)).
    apply PMF.in_find_iff in Hin. exact (Hin (eq_sym E)).
Defined.

Inductive AnalysisResult (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type :=
| AnalysisOK     (facts : CompilationFacts p ip)
| AnalysisFailed (ds : list (DiagnosticReason p)) (Hne : ds <> nil).
Arguments AnalysisOK {p ip} _.
Arguments AnalysisFailed {p ip} _ _.

Record ProgramAnalysis (p : GoProgram) : Type := mkProgramAnalysis {
  pa_indexed : GoIndex.IndexedProgram p;
  pa_result  : AnalysisResult p pa_indexed
}.
Arguments mkProgramAnalysis {p} _ _.
Arguments pa_indexed {p} _.
Arguments pa_result {p} _.

Definition list_is_nil {A} (l : list A) : {l = nil} + {l <> nil}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(** validity is DERIVED from an empty diagnostic list (the decision IS the diagnostic pass) — not a peer check. *)
Definition analyze_valid_of_no_diags (p : GoProgram) (ip : GoIndex.IndexedProgram p) :
  collect_diagnostics p (GoIndex.indexed_syntax ip) = nil -> ProgValid p :=
  fun He => proj1 (analysis_ok_b_ProgValid p) (proj1 (collect_diagnostics_empty_iff p (GoIndex.indexed_syntax ip)) He).

(** §14 — the ONE analysis pass.  The shared collections — the index, the visit stream, the occurrence status
    map, and the package buckets — are computed ONCE (let-bound) and feed BOTH the accept/reject decision AND
    the successful [CompilationFacts]: the expression facts and the diagnostics are two linear passes over the
    SAME [visit]/[status], and the [buckets] serve BOTH the package diagnostics ([bucket_diags_elems] — the
    package acceptance is the bucket LENGTHS, never [package_summaries]) and the retained facts.
    There is no separate [analysis_facts] recomputation.  The DECISION is exactly "the diagnostic pass produced
    nothing"; on success the retained facts are exposed with the derived validity, on failure the EXACT
    diagnostic list.  ([diags] is definitionally [collect_diagnostics p idx], so the decision theorems below are
    unchanged.) *)
Definition analyze_indexed (p : GoProgram) (ip : GoIndex.IndexedProgram p) : AnalysisResult p ip :=
  let idx     := GoIndex.indexed_syntax ip in
  let blocks  := prog_blocks p in                (* the per-file visit blocks, retained ONCE *)
  let visit   := concat blocks in                (* = prog_visit p — the flattened analysis stream *)
  let status  := fold_right psm_step (GoIndex.NodeKeyMapBase.empty (option ConstInfo)) visit in
  let buckets := fold_right (ppkg_step idx) (PM.empty (list (GoIndex.DeclRef p))) visit in
  let facts   := fold_right (add_occ_fact_sm status) (GoIndex.NodeKeyMapBase.empty ExprFact) visit in
  let raw     := flat_map (fun roc => occ_expr_diags_sm status idx (snd roc) (fst roc))
                          (flat_map (annotate_encl idx []) blocks)   (* = annotate_program idx *)
                   ++ bucket_diags_elems buckets (bucket_key_present idx)
                        (PM.elements buckets) (elements_all_mapsto buckets) in
  (* §16 canonical order: node-primary diagnostics bucketed by NodeKey + flattened, then package-primary. *)
  let diags   := bucket_flatten dcode (node_keyed raw) ++ pkg_primary raw in
  match list_is_nil diags with
  | left He  => AnalysisOK (mkCompilationFacts
                  (mkExprFactTable facts (prog_expr_facts_domain p) (prog_expr_facts_find p))
                  buckets
                  (prog_package_refs_present idx)
                  (prog_package_refs_bucket_len idx)
                  (prog_package_refs_belongs idx)
                  (analyze_valid_of_no_diags p ip He))
  | right Hne => AnalysisFailed diags Hne
  end.

Definition analyze (p : GoProgram) : ProgramAnalysis p :=
  let ip := GoIndex.index_program p in
  mkProgramAnalysis ip (analyze_indexed p ip).

(** ANALYSIS EXACTNESS: analysis succeeds (exposes facts) IFF the program is valid ([ProgValid] = [GoCompile]);
    it fails (exposes nonempty diagnostics) IFF the program is invalid.  Success and failure are exclusive. *)
Theorem analyze_ok_iff_ProgValid (p : GoProgram) :
  (exists facts, pa_result (analyze p) = AnalysisOK facts) <-> ProgValid p.
Proof.
  unfold analyze, analyze_indexed; cbn [pa_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - split; intro Hx; [ apply (analyze_valid_of_no_diags p (GoIndex.index_program p) He) | eexists; reflexivity ].
  - split; intro Hx.
    + destruct Hx as [facts Hf]; discriminate Hf.
    + exfalso. apply Hne, (collect_diagnostics_empty_iff p _), (analysis_ok_b_ProgValid p); exact Hx.
Qed.

Theorem analyze_failed_iff_not_ProgValid (p : GoProgram) :
  (exists ds Hne, pa_result (analyze p) = AnalysisFailed ds Hne) <-> ~ ProgValid p.
Proof.
  unfold analyze, analyze_indexed; cbn [pa_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - split; intro Hx.
    + destruct Hx as [ds [Hne Hf]]; discriminate Hf.
    + exfalso. apply Hx, (analyze_valid_of_no_diags p (GoIndex.index_program p) He).
  - split; intro Hx.
    + intro Hv. apply Hne, (collect_diagnostics_empty_iff p _), (analysis_ok_b_ProgValid p); exact Hv.
    + eexists; eexists; reflexivity.
Qed.

(** on failure the exposed diagnostics ARE the canonical [collect_diagnostics] (used to project the legacy class). *)
Lemma analyze_failed_ds (p : GoProgram) ds Hne :
  pa_result (analyze p) = AnalysisFailed ds Hne ->
  ds = collect_diagnostics p (GoIndex.indexed_syntax (GoIndex.index_program p)).
Proof.
  unfold analyze, analyze_indexed; cbn [pa_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hn] end.
  - intro H; discriminate H.
  - intro H. inversion H. reflexivity.
Qed.

(** A failed analysis result is incompatible with validity (used to discharge the impossible branch when
    minting the provenance sigma from a validity proof). *)
Lemma analyze_failed_not_valid (p : GoProgram) ds Hne :
  pa_result (analyze p) = AnalysisFailed ds Hne -> ProgValid p -> False.
Proof.
  intros Heq Hv.
  exact (proj1 (analyze_failed_iff_not_ProgValid p) (ex_intro _ ds (ex_intro _ Hne Heq)) Hv).
Qed.

(** The one production analysis result, CASE-SPLIT into its OK / Failed shape WITH the defining equation
    retained (a plain [match] on the retained [pa_result], not a proof-mode convoy fight): every downstream
    [go_compile] fact is derived from this, so nothing re-destructs [analyze] under its dependent motive. *)
Definition analyze_result_cases (p : GoProgram) :
  {facts : CompilationFacts p (pa_indexed (analyze p)) & pa_result (analyze p) = AnalysisOK facts} +
  {ds : list (DiagnosticReason p) & {Hne : ds <> nil & pa_result (analyze p) = AnalysisFailed ds Hne}} :=
  match pa_result (analyze p) as r
    return pa_result (analyze p) = r ->
      {facts : CompilationFacts p (pa_indexed (analyze p)) & pa_result (analyze p) = AnalysisOK facts} +
      {ds : list (DiagnosticReason p) & {Hne : ds <> nil & pa_result (analyze p) = AnalysisFailed ds Hne}}
  with
  | AnalysisOK facts      => fun Heq => inl (existT _ facts Heq)
  | AnalysisFailed ds Hne => fun Heq => inr (existT _ ds (existT _ Hne Heq))
  end eq_refl.

(** From a validity proof, the EXACT [AnalysisOK] result + its facts (the failed branch is impossible).  This
    is the provenance witness a [CompilableProgram] must carry: the stored facts ARE [analyze]'s output. *)
Definition analyze_ok_sig (p : GoProgram) (H : ProgValid p) :
  {facts : CompilationFacts p (pa_indexed (analyze p)) & pa_result (analyze p) = AnalysisOK facts} :=
  match analyze_result_cases p with
  | inl s => s
  | inr b => False_rect _
      (analyze_failed_not_valid p (projT1 b) (projT1 (projT2 b)) (projT2 (projT2 b)) H)
  end.

(** [GoCompile p] IS whole-program admissibility: the program is typed through [GoTypes] AND every package
    has exactly one `main`.  The package clause is now SOURCE-owned (each file's [source_package]), rendered
    by [GoRender] — it is no longer a compiler-derived fact, so there is no [cf_pkg_name].  The RICHER
    per-program [CompilationFacts] record (the occurrence-keyed [ExprFactTable] + package `main`-ref buckets +
    validity) IS retained — by a successful [analyze]/[CompilableProgram] (`cp_facts`) — decorating this same
    program without a second AST; there is no unused placeholder. *)
Definition GoCompile (p : GoProgram) : Prop := ProgValid p.

(** ---- destructuring the ONE retained [analyze] WITHOUT re-projection: record eta re-assembles the analysis
    from its projections, so a component-level [pa_result] fact lifts to a WHOLE-analysis equation
    ([analyze p = mkProgramAnalysis ip (AnalysisOK/Failed …)] — homogeneous, no index transport).  The
    non-dependent [analysis_ok_flag] lets such a whole equation discriminate OK-vs-Failed by [rewrite] (no
    dependent [f_equal] over the indexed [pa_result]). ---- *)
Lemma program_analysis_eta {p} (a : ProgramAnalysis p) :
  a = mkProgramAnalysis (pa_indexed a) (pa_result a).
Proof. destruct a; reflexivity. Qed.

Definition result_ok_b {p ip} (r : AnalysisResult p ip) : bool :=
  match r with AnalysisOK _ => true | AnalysisFailed _ _ => false end.
Definition analysis_ok_flag {p} (a : ProgramAnalysis p) : bool := result_ok_b (pa_result a).

Lemma analysis_ok_flag_of_valid : forall p, ProgValid p -> analysis_ok_flag (analyze p) = true.
Proof. intros p Hv. unfold analysis_ok_flag. destruct (analyze_ok_sig p Hv) as [facts Heq]. rewrite Heq. reflexivity. Qed.

Lemma analyze_ok_whole : forall p facts, pa_result (analyze p) = AnalysisOK facts ->
  analyze p = mkProgramAnalysis (pa_indexed (analyze p)) (AnalysisOK facts).
Proof.
  intros p facts H.
  transitivity (mkProgramAnalysis (pa_indexed (analyze p)) (pa_result (analyze p))).
  - apply program_analysis_eta.
  - rewrite H. reflexivity.
Qed.

Lemma analyze_failed_whole : forall p ds Hne, pa_result (analyze p) = AnalysisFailed ds Hne ->
  analyze p = mkProgramAnalysis (pa_indexed (analyze p)) (AnalysisFailed ds Hne).
Proof.
  intros p ds Hne H.
  transitivity (mkProgramAnalysis (pa_indexed (analyze p)) (pa_result (analyze p))).
  - apply program_analysis_eta.
  - rewrite H. reflexivity.
Qed.

Lemma analyze_whole_failed_not_valid : forall p ip ds Hne,
  analyze p = mkProgramAnalysis ip (AnalysisFailed ds Hne) -> ProgValid p -> False.
Proof.
  intros p ip ds Hne Hw Hv.
  pose proof (analysis_ok_flag_of_valid p Hv) as Hok.
  rewrite Hw in Hok. discriminate Hok.
Qed.

(** the witness-path destructuring: match the whole retained analysis EXACTLY ONCE, binding its retained index
    [ip] and result; validity rules the Failed branch impossible.  [ip] and [facts] come from the SAME
    evaluation — never a [pa_indexed (analyze p)] re-projection. *)
Definition analyze_ok_full (p : GoProgram) (H : ProgValid p) :
  {ip : GoIndex.IndexedProgram p & {facts : CompilationFacts p ip | analyze p = mkProgramAnalysis ip (AnalysisOK facts)}} :=
  match analyze p as a
    return (analyze p = a ->
      {ip : GoIndex.IndexedProgram p & {facts : CompilationFacts p ip | analyze p = mkProgramAnalysis ip (AnalysisOK facts)}})
  with
  | mkProgramAnalysis ip res =>
      fun Ha =>
      match res as r
        return (res = r ->
          {ip0 : GoIndex.IndexedProgram p & {facts : CompilationFacts p ip0 | analyze p = mkProgramAnalysis ip0 (AnalysisOK facts)}})
      with
      | AnalysisOK facts      => fun Hr =>
          existT _ ip (exist _ facts (eq_trans Ha (f_equal (mkProgramAnalysis ip) Hr)))
      | AnalysisFailed ds Hne => fun Hr =>
          False_rect _ (analyze_whole_failed_not_valid p ip ds Hne (eq_trans Ha (f_equal (mkProgramAnalysis ip) Hr)) H)
      end eq_refl
  end eq_refl.

(** §18/§21 (C3) — a compiled program RETAINS the ONE evaluated analysis by DESTRUCTURING it: the original
    program, the EXACT analyzed [IndexedProgram] ([cp_index]) BOUND from that analysis, and its
    [CompilationFacts] indexed BY that retained index ([cp_facts : CompilationFacts cp_program cp_index] — no
    [pa_indexed (analyze …)] re-projection).  The mandatory [cp_prov] field PROVES the WHOLE retained analysis
    IS this record ([analyze cp_program = mkProgramAnalysis cp_index (AnalysisOK cp_facts)] — a HOMOGENEOUS
    equation, no index transport, pinning index + facts + success together).  There is therefore NO way to
    construct a [CompilableProgram] for a program [analyze] rejects, the index is never reconstructed, and
    there is no parallel capability path.  [cp_ok] projects the retained facts' validity.  [cp_program] stays a
    direct first-field projection, so rendering/emission never reduce [analyze] (the opaque,
    vm-compute-unfriendly index — the F5 constraint). *)
Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_index   : GoIndex.IndexedProgram cp_program;
  cp_facts   : CompilationFacts cp_program cp_index;
  cp_prov    : analyze cp_program = mkProgramAnalysis cp_index (AnalysisOK cp_facts)
}.

Definition cp_ok (cp : CompilableProgram) : GoCompile (cp_program cp) := cf_valid (cp_facts cp).

(** the PROVENANCE surfaces: every [CompilableProgram]'s WHOLE retained analysis IS this record — index +
    facts + success together ([analyze cp_program = mkProgramAnalysis cp_index (AnalysisOK cp_facts)]); the
    retained index therefore IS [analyze]'s (the projection retains, it does not reconstruct). *)
Theorem compilable_prov : forall cp : CompilableProgram,
  analyze (cp_program cp) = mkProgramAnalysis (cp_index cp) (AnalysisOK (cp_facts cp)).
Proof. intro cp; exact (cp_prov cp). Qed.

Theorem compilable_index_retained : forall cp : CompilableProgram,
  cp_index cp = pa_indexed (analyze (cp_program cp)).
Proof. intro cp. rewrite (cp_prov cp). reflexivity. Qed.

(** The compiled evidence EXPOSES that the same program is typed through [GoTypes] (§17): an immediate
    canonical projection, not a stored second copy of the typing proof. *)
Theorem compile_program_typed : forall p, GoCompile p -> ProgramTyped p.
Proof. intros p H; exact (proj1 H). Qed.

Theorem compilable_program_typed : forall cp : CompilableProgram, ProgramTyped (cp_program cp).
Proof. intro cp; exact (compile_program_typed _ (cp_ok cp)). Qed.

(** ---- the proof-producing executable compiler ---- *)

Inductive result (E A : Type) : Type := Ok : A -> result E A | Err : E -> result E A.
Arguments Ok {E A}. Arguments Err {E A}.

Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** §18 — a structured failure bundle: the EXACT analysis diagnostics + their nonempty proof. *)
Record CompileFailure (p : GoProgram) : Type := mkCompileFailure {
  cfail_diags    : list (DiagnosticReason p) ;
  cfail_nonempty : cfail_diags <> nil
}.
Arguments mkCompileFailure {p} _ _.
Arguments cfail_diags {p} _.
Arguments cfail_nonempty {p} _.

Inductive CompileOutcome (p : GoProgram) : Type :=
| CompiledOk    (cp : CompilableProgram) (Hcp : cp_program cp = p)
| CompileFailed (fail : CompileFailure p).
Arguments CompiledOk {p} _ _.
Arguments CompileFailed {p} _.

(** the LEGACY coarse class, a PROJECTION of the analysis diagnostics (never a separate check): a typing-class
    diagnostic dominates, else a package-class diagnostic, else success. *)
Inductive LegacyCompileClass : Type := LCOk | LCTyping | LCPackageMainCount.
Definition legacy_class_of_diags {p} (ds : list (DiagnosticReason p)) : LegacyCompileClass :=
  if existsb diag_is_typing ds then LCTyping
  else if existsb diag_is_package ds then LCPackageMainCount else LCOk.
Definition legacy_compile_class {p} (o : CompileOutcome p) : LegacyCompileClass :=
  match o with CompiledOk _ _ => LCOk | CompileFailed fail => legacy_class_of_diags (cfail_diags fail) end.

(** §18 — the production compiler DESTRUCTURES the ONE retained [analyze] EXACTLY ONCE: [outcome_of_analysis]
    matches the WHOLE [ProgramAnalysis] (binding its retained index [ip] and result), so [AnalysisOK] mints a
    [CompilableProgram] whose [cp_index] IS that bound [ip] (never a [pa_indexed] re-projection) and whose
    [cp_prov] is [analyze p = mkProgramAnalysis ip (AnalysisOK facts)] (built from the two match equations).
    Failure CARRIES the exact analysis diagnostics — never a second checker or a coarse recomputation. *)
Definition outcome_of_analysis (p : GoProgram) (a : ProgramAnalysis p) :
  analyze p = a -> CompileOutcome p :=
  match a as a0 return (analyze p = a0 -> CompileOutcome p) with
  | mkProgramAnalysis ip res =>
      fun Ha =>
      match res as r return (res = r -> CompileOutcome p) with
      | AnalysisOK facts      => fun Hr =>
          CompiledOk (mkCompilable p ip facts (eq_trans Ha (f_equal (mkProgramAnalysis ip) Hr))) eq_refl
      | AnalysisFailed ds Hne => fun _  => CompileFailed (mkCompileFailure ds Hne)
      end eq_refl
  end.

Definition go_compile (p : GoProgram) : CompileOutcome p :=
  outcome_of_analysis p (analyze p) eq_refl.

(** the two computation facts of [outcome_of_analysis], stated over the whole analysis pinned to a constructor:
    the nested matches collapse by iota (no dependent-convoy reasoning against [analyze]). *)
Lemma outcome_of_analysis_ok_eq : forall p ip facts (Ha : analyze p = mkProgramAnalysis ip (AnalysisOK facts)),
  outcome_of_analysis p (mkProgramAnalysis ip (AnalysisOK facts)) Ha = CompiledOk (mkCompilable p ip facts Ha) eq_refl.
Proof. intros p ip facts Ha. reflexivity. Qed.

Lemma outcome_of_analysis_failed_eq : forall p ip ds Hne (Ha : analyze p = mkProgramAnalysis ip (AnalysisFailed ds Hne)),
  outcome_of_analysis p (mkProgramAnalysis ip (AnalysisFailed ds Hne)) Ha = CompileFailed (mkCompileFailure ds Hne).
Proof. intros p ip ds Hne Ha. reflexivity. Qed.

(** the shape facts over a genuine ANALYSIS VARIABLE [a] equal to a constructor: [subst] collapses the nested
    matches by iota — no dependent [rewrite] against [analyze] under a binder. *)
Lemma outcome_of_analysis_eq_ok : forall p (a : ProgramAnalysis p) (Ha : analyze p = a) ip facts,
  a = mkProgramAnalysis ip (AnalysisOK facts) ->
  exists cp Hcp, outcome_of_analysis p a Ha = CompiledOk cp Hcp.
Proof.
  intros p a Ha ip facts Heq. revert Ha. rewrite Heq. intro Ha.
  exists (mkCompilable p ip facts Ha). exists eq_refl. apply outcome_of_analysis_ok_eq.
Qed.

Lemma outcome_of_analysis_eq_failed : forall p (a : ProgramAnalysis p) (Ha : analyze p = a) ip ds Hne,
  a = mkProgramAnalysis ip (AnalysisFailed ds Hne) ->
  outcome_of_analysis p a Ha = CompileFailed (mkCompileFailure ds Hne).
Proof.
  intros p a Ha ip ds Hne Heq. revert Ha. rewrite Heq. intro Ha. apply outcome_of_analysis_failed_eq.
Qed.

Lemma go_compile_ok_shape : forall p ip facts,
  analyze p = mkProgramAnalysis ip (AnalysisOK facts) ->
  exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p ip facts Hp. unfold go_compile.
  exact (outcome_of_analysis_eq_ok p (analyze p) eq_refl ip facts Hp).
Qed.

Lemma go_compile_failed_shape : forall p ip ds Hne,
  analyze p = mkProgramAnalysis ip (AnalysisFailed ds Hne) ->
  go_compile p = CompileFailed (mkCompileFailure ds Hne).
Proof.
  intros p ip ds Hne Hp. unfold go_compile.
  exact (outcome_of_analysis_eq_failed p (analyze p) eq_refl ip ds Hne Hp).
Qed.

(** (A) internal exactness: [go_compile] succeeds exactly on admissible programs, whole-program.  Success value
    carries its OWN validity (via [cf_valid (cp_facts cp)]) and program identity (via [Hcp]) — derivable from
    the compiled artifact's fields regardless of HOW it was produced. *)
Theorem go_compile_ok_valid : forall p cp Hcp,
  go_compile p = CompiledOk cp Hcp -> cp_program cp = p /\ GoCompile (cp_program cp).
Proof.
  intros p cp Hcp _. split; [ exact Hcp | exact (cf_valid (cp_facts cp)) ].
Qed.

Theorem go_compile_complete : forall p,
  GoCompile p -> exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p Hvalid.
  destruct (analyze_ok_sig p Hvalid) as [ facts Heq ].
  exact (go_compile_ok_shape p (pa_indexed (analyze p)) facts (analyze_ok_whole p facts Heq)).
Qed.

(** fixture helper: acceptance through the theorems. *)
Lemma go_compile_ok_of_prog_ok : forall p, prog_ok p = true -> exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof. intros p H; apply go_compile_complete, (proj1 (prog_ok_iff p)); exact H. Qed.

(** the witness builder: from validity, [analyze_ok_full] destructures [analyze p] ONCE, delivering the bound
    retained index [ip], its [CompilationFacts], and the whole-analysis provenance.  That single execution is
    let-bound and all three constructor arguments PROJECT it — [cp_index], [cp_facts], and [cp_prov] come from
    ONE analysis, never three reruns.  [cp_program] is a direct first-field projection ([= p]) so
    rendering/emission never reduce the (opaque, vm-compute-unfriendly) index analysis (F5).  This is the SAME
    single-destructuring provenance [go_compile]'s success value carries — the two artifacts are built ONE way. *)
Definition compilable_of_valid (p : GoProgram) (H : GoCompile p) : CompilableProgram :=
  let s  := analyze_ok_full p H in
  let fs := projT2 s in
  mkCompilable p (projT1 s) (proj1_sig fs) (proj2_sig fs).

(** fixture helper: a non-typed program is REJECTED at the TYPING legacy class — a projection of the carried
    diagnostics, never a [program_typedb] rerun. *)
Lemma go_compile_untyped : forall p, program_typedb p = false -> legacy_compile_class (go_compile p) = LCTyping.
Proof.
  intros p Hf.
  destruct (analyze_result_cases p) as [ [facts Hok] | [ds [Hne Hfail]] ].
  - exfalso. assert (Hv : ProgValid p) by (apply (analyze_ok_iff_ProgValid p); exists facts; exact Hok).
    pose proof (proj2 (program_typedb_iff p) (proj1 Hv)) as Ht. rewrite Ht in Hf; discriminate Hf.
  - rewrite (go_compile_failed_shape p (pa_indexed (analyze p)) ds Hne (analyze_failed_whole p ds Hne Hfail)).
    cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (analyze_failed_ds p ds Hne Hfail), existsb_typing_collect, Hf. reflexivity.
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

(* [prog_ok] is exactly the conjunction of the two decision halves. *)
Lemma prog_ok_eq : forall p, prog_ok p = program_typedb p && pkg_all_ok p.
Proof. reflexivity. Qed.

(** the [go_compile] LEGACY CLASS (a projection of the carried diagnostics) — invariant under file insertion
    order.  It matches the decision: success -> [LCOk]; not typed -> [LCTyping]; typed but bad package -> [LCPackageMainCount]. *)
Definition go_compile_class (p : GoProgram) : LegacyCompileClass := legacy_compile_class (go_compile p).

Lemma go_compile_class_spec : forall p,
  go_compile_class p
  = (if prog_ok p then LCOk else if program_typedb p then LCPackageMainCount else LCTyping).
Proof.
  intro p. unfold go_compile_class.
  destruct (analyze_result_cases p) as [ [facts Hok] | [ds [Hne Hfail]] ].
  - assert (Hpv : ProgValid p) by (apply (analyze_ok_iff_ProgValid p); exists facts; exact Hok).
    destruct (go_compile_ok_shape p (pa_indexed (analyze p)) facts (analyze_ok_whole p facts Hok)) as [cp [Hcp Hgo]]. rewrite Hgo.
    cbn [legacy_compile_class]. rewrite (proj2 (prog_ok_iff p) Hpv). reflexivity.
  - assert (Hnv : ~ ProgValid p)
      by (apply (analyze_failed_iff_not_ProgValid p); exists ds; exists Hne; exact Hfail).
    assert (Hpf : prog_ok p = false)
      by (destruct (prog_ok p) eqn:Ep; [ exfalso; apply Hnv, (proj1 (prog_ok_iff p)); exact Ep | reflexivity ]).
    rewrite Hpf. rewrite (go_compile_failed_shape p (pa_indexed (analyze p)) ds Hne (analyze_failed_whole p ds Hne Hfail)).
    cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (analyze_failed_ds p ds Hne Hfail), existsb_typing_collect, existsb_package_collect.
    destruct (program_typedb p) eqn:Ht; cbn [negb].
    + assert (Hpk : pkg_all_ok p = false) by (rewrite prog_ok_eq, Ht, Bool.andb_true_l in Hpf; exact Hpf).
      rewrite Hpk. reflexivity.
    + reflexivity.
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
Example over_program_rejected  : legacy_compile_class (go_compile over_program) = LCTyping.    Proof. exact (go_compile_untyped _ over_program_untyped). Qed.
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
Example int_program_compiles : exists cp Hcp, go_compile int_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_prog_ok _ int_program_ok). Qed.

(** A program whose only argument is [uint8(int(300))] — a valid inner [int(300)] whose value does NOT fit
    the outer [uint8]; the invalid nested conversion cannot be revived, so the whole program is rejected. *)
Definition bad_convert_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IUint8 (EIntConvert IInt (EInt 300)) ] ] ].
Example bad_convert_untyped     : program_typedb bad_convert_program = false. Proof. vm_compute; reflexivity. Qed.
Example bad_convert_rejected    : legacy_compile_class (go_compile bad_convert_program) = LCTyping. Proof. exact (go_compile_untyped _ bad_convert_untyped). Qed.
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
Example str_program_compiles : exists cp Hcp, go_compile str_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_prog_ok _ str_program_ok). Qed.

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
Example float_program_compiles : exists cp Hcp, go_compile float_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_prog_ok _ float_program_ok). Qed.

Definition float_reject_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IInt (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ].   (* int(3.5): fractional *)
Example float_reject_untyped    : program_typedb float_reject_program = false. Proof. vm_compute. reflexivity. Qed.
Example float_reject_rejected   : legacy_compile_class (go_compile float_reject_program) = LCTyping.
Proof. exact (go_compile_untyped _ float_reject_untyped). Qed.
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
Example complex_program_compiles : exists cp Hcp, go_compile complex_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_prog_ok _ complex_program_ok). Qed.

Definition complex_overflow_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EComplexConvert C64 (EComplex (mkDC (mkDecimal 1 39 eq_refl) (mkDecimal 0 0 eq_refl))) ] ] ].
Example complex_overflow_untyped    : program_typedb complex_overflow_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_overflow_rejected   : legacy_compile_class (go_compile complex_overflow_program) = LCTyping. Proof. exact (go_compile_untyped _ complex_overflow_untyped). Qed.
Example complex_overflow_no_compile : ~ GoCompile complex_overflow_program.
Proof. apply (reject_no_compile complex_overflow_program); vm_compute; reflexivity. Qed.

Definition complex_nonzero_imag_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EIntConvert IInt (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 1 0 eq_refl))) ] ] ].
Example complex_nonzero_imag_untyped    : program_typedb complex_nonzero_imag_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_rejected   : legacy_compile_class (go_compile complex_nonzero_imag_program) = LCTyping. Proof. exact (go_compile_untyped _ complex_nonzero_imag_untyped). Qed.
Example complex_nonzero_imag_no_compile : ~ GoCompile complex_nonzero_imag_program.
Proof. apply (reject_no_compile complex_nonzero_imag_program); vm_compute; reflexivity. Qed.

(** ============================================================================================================
    §22/§23 (C3 FINAL) — CONCRETE STRUCTURED-DIAGNOSTIC FIXTURES.  Because the occurrence index is an OPAQUE
    sealed module ([Snap : SNAP_SIG]), the analysis ([analyze]/[expr_diags]/[pkg_diags]/[erased_report]) does
    NOT reduce — a fixture cannot [vm_compute] a concrete report.  So each fixture pins the REAL index
    ([Snap.index_program] of the concrete program) and states its structured claim THROUGH the proven
    soundness/determinism/emptiness bridges.  Non-vacuity comes from the COMPUTABLE type checker
    ([program_typedb]/[pkg_all_ok], which DO reduce): a rejected program has a provably NON-EMPTY report
    ([*_empty_iff] contrapositive), and every diagnostic in it is pinned by the family soundness theorem.
    ============================================================================================================ *)

Definition c3_ms : ModuleSpec := mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23.

(** ---- §22.15 — REORDERED CONSTRUCTION: the SAME semantic file map built from PERMUTED [GoFileNode] input has
    a byte-identical erased diagnostic report, the identical success/failure class, and the identical canonical
    fact enumeration — construction order is not observable. ---- *)
Definition rnode_a : GoFileNode := main_file_node (mkFP "a.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ].
Definition rnode_b : GoFileNode := main_file_node (mkFP "b.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ].

Example reorder_builds1 : exists p, build_program c3_ms [rnode_a; rnode_b] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.
Example reorder_builds2 : exists p, build_program c3_ms [rnode_b; rnode_a] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.

Theorem reorder_construction_deterministic :
  forall p1 p2 (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2),
    build_program c3_ms [rnode_a; rnode_b] = Some p1 ->
    build_program c3_ms [rnode_b; rnode_a] = Some p2 ->
    erased_report p1 idx1 = erased_report p2 idx2
    /\ go_compile_class p1 = go_compile_class p2
    /\ GoIndex.NodeKeyMapBase.elements (prog_expr_facts p1) = GoIndex.NodeKeyMapBase.elements (prog_expr_facts p2).
Proof.
  intros p1 p2 idx1 idx2 H1 H2.
  assert (HFE : GoAST.FilesEqual (prog_files p1) (prog_files p2)).
  { unfold build_program in H1, H2.
    destruct (filemap_of_nodes [rnode_a; rnode_b]) as [fm1|] eqn:F1; [ | discriminate ].
    destruct (filemap_of_nodes [rnode_b; rnode_a]) as [fm2|] eqn:F2; [ | discriminate ].
    injection H1 as <-. injection H2 as <-. cbn [prog_files].
    exact (filemap_of_nodes_permutation _ _ fm1 fm2 (perm_swap rnode_b rnode_a []) F1 F2). }
  split; [ exact (erased_report_FilesEqual p1 p2 idx1 idx2 HFE) |].
  split; [ exact (go_compile_class_Equal p1 p2 HFE) | exact (prog_expr_facts_enum_FilesEqual p1 p2 HFE) ].
Qed.

(** ---- §22.13 — EMPTY PROGRAM: the module-only program is ACCEPTED with an EMPTY erased report and an EMPTY
    fact enumeration (no package to type, no `main` required). ---- *)
Theorem empty_program_report :
  erased_report (empty_program c3_ms) (GoIndex.Snap.index_program (empty_program c3_ms)) = nil
  /\ GoIndex.NodeKeyMapBase.elements (prog_expr_facts (empty_program c3_ms)) = nil.
Proof.
  split.
  - apply (proj2 (erased_report_empty_iff (empty_program c3_ms) _)).
    rewrite analysis_ok_b_prog_ok. apply prog_ok_empty.
  - vm_compute. reflexivity.
Qed.

(** ---- §22.8 — NESTED INVALID CONVERSION [float64(int8(128))]: the program is REJECTED, so its expression
    report is genuinely NON-EMPTY, and EVERY invalid-conversion diagnostic in it carries a same-file,
    nearest-first, duplicate-free STRICT-ANCESTOR conversion context (the outer [float64] strictly encloses the
    primary [int8] — never fabricated syntax). ---- *)
Definition nested_conv_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EFloatConvert F64 (EIntConvert IInt8 (EInt 128)) ] ] ].

Example nested_conv_untyped : program_typedb nested_conv_program = false.
Proof. vm_compute. reflexivity. Qed.

(* the EXACT whole erased report: EXACTLY ONE diagnostic, code DCInvalidConversion, PRIMARY anchored at the
   inner [int8] conversion (local 6), the outer [float64] conversion (local 5) in the RELATED context, and the
   target payload [TInteger IInt8].  Computed through the source characterization of the report — non-vacuous,
   exact count, exact anchors, exact payload. *)
Theorem nested_conv_erased_report :
  erased_report nested_conv_program (GoIndex.Snap.index_program nested_conv_program)
  = [ mkErasedDiagnostic DCInvalidConversion
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) ]
        (Some (TInteger IInt8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ---- §22.9/§22.11 — THREE MAINS IN ONE PACKAGE: the program is REJECTED (a package with != 1 main), so its
    package report is genuinely NON-EMPTY, and EVERY duplicate-main diagnostic names a strictly-later,
    genuinely-DISTINCT main in the SAME package, with the related [earlier] the unique smallest-NodeKey main. ---- *)
Definition three_main_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt 1 ] ]; DMain [ SPrintln [ EInt 2 ] ]; DMain [ SPrintln [ EInt 3 ] ] ].

(* the EXACT whole erased report: EXACTLY TWO DCDuplicateMain diagnostics — the SECOND main (local 6) and the
   THIRD main (local 9) each PRIMARY, both RELATED to the FIRST canonical main (local 3, the smallest key).  No
   third diagnostic, no self-relation, no missing-main. *)
Theorem three_main_erased_report :
  erased_report three_main_program (GoIndex.Snap.index_program three_main_program)
  = [ mkErasedDiagnostic DCDuplicateMain
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 3%positive) ] None
    ; mkErasedDiagnostic DCDuplicateMain
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 9%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 3%positive) ] None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ---- §22.12 — PACKAGE WITH NO MAIN: a represented package whose only file declares NO `main` is REJECTED, so
    its package report is genuinely NON-EMPTY, and EVERY missing-main diagnostic anchors a genuinely represented
    package that contains EXACTLY ZERO `main` declarations (no fake file/node primary). ---- *)
Definition missing_main_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl) [ ].

(* the EXACT whole erased report: EXACTLY ONE DCMissingMain, anchored at the represented package (root "") —
   a PACKAGE anchor, never a fake file/node primary — with no related anchor and no target payload. *)
Theorem missing_main_erased_report :
  erased_report missing_main_program (GoIndex.Snap.index_program missing_main_program)
  = [ mkErasedDiagnostic DCMissingMain (EAPackage "") [] None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ---- §23 — the EXACT expression-fact query: on ANY valid [CompilationFacts], EVERY expression reference's
    queried fact is its occurrence's EXACT source-derived fact — the [ef_const_status] IS the occurrence's
    [const_info] and the [ef_use_resolved] IS its use-context resolution ([resolve_expr_const], rounded ONCE at
    conversion — no rerounding).  So the query PROJECTS the occurrence, never a recomputed value. ---- *)
Lemma expr_fact_at_exact {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) :
  exists e ci,
    GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some e
    /\ const_info e = Some ci
    /\ expr_fact_at facts er
       = mkExprFact ci (occ_use_resolved (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))).
Proof.
  assert (Hkind : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = GoIndex.KExpression)
    by exact (proj2_sig er).
  destruct (GoIndex.kind_view_expr _ Hkind) as [e Hv].
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref er)) as Hin.
  pose proof (proj2 (GoTypes.program_typedb_iff p) (proj1 (cf_valid facts))) as HPT.
  destruct (prog_visit_const_info_some p HPT (GoIndex.erase_ref er)
              (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) e Hin Hv) as [ci Hci].
  pose proof (eft_complete (cf_expr_facts facts) (GoIndex.erase_ref er)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) Hin) as Hfind.
  rewrite (occ_expr_fact_status _ e ci Hv Hci) in Hfind.
  exists e, ci. split; [exact Hv | split; [exact Hci | exact (expr_fact_at_find facts er _ Hfind)]].
Qed.

Definition fact_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EFloatConvert F64 (EIntConvert IInt (EInt 5)) ] ] ].
Example fact_program_ok : prog_ok fact_program = true. Proof. vm_compute. reflexivity. Qed.

(** §23 — the EXACT per-occurrence facts of the VALID nested-conversion program [float64(int(5))].  The whole
    fact enumeration (three expression occurrences), projected to (local id, typed-target-if-any,
    [resolved_type_at]): the inner literal [5] (local 7) is UNTYPED and unresolved; the inner conversion
    [int(5)] (local 6) is TYPED at [TInteger IInt] and unresolved (a conversion operand); the outer println
    argument [float64(...)] (local 5) is TYPED at [TFloat F64] and RESOLVES to [TFloat F64] — exactly the GoTypes
    use-resolution, no rerounding. *)
Theorem fact_program_facts_exact :
  map (fun kv => (GoIndex.nk_local (fst kv),
                  match ef_const_status (snd kv) with CIUntyped _ => None | CITyped t _ => Some t end,
                  resolved_type_at (snd kv)))
      (GoIndex.NodeKeyMapBase.elements (prog_expr_facts fact_program))
  = [ (5%positive, Some (TFloat F64), Some (TFloat F64))
    ; (6%positive, Some (TInteger IInt), None)
    ; (7%positive, None, None) ].
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the two scalar occurrences carry their EXACT constants: the inner literal is the UNTYPED [CInt 5] (unresolved
   operand), the inner conversion is the TYPED [int(5)] (unresolved operand). *)
Theorem fact_program_inner_literal :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 7%positive) (prog_expr_facts fact_program)
  = Some (mkExprFact (CIUntyped (CInt 5)) None).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

Theorem fact_program_inner_conversion :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive) (prog_expr_facts fact_program)
  = Some (mkExprFact (CITyped (TInteger IInt) (TCInteger IInt 5 eq_refl)) None).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the OUTER println argument [float64(int(5))]: its EXACT resolved constant is the rational [5/1] at [TFloat
   F64] — not merely "some float64".  [ef_const_status] is [CITyped (TFloat F64)], [resolved_type_at] is [TFloat
   F64], the resolved GoConst is [CFloat] with numerator 5 / denominator 1, and it resolves. *)
Theorem fact_program_outer_arg :
  option_map (fun f =>
     (match ef_const_status f with CITyped t _ => Some t | CIUntyped _ => None end,
      resolved_type_at f,
      match resolved_constant_at f with Some (CFloat fc) => Some (fc_num fc, fc_den fc) | _ => None end,
      match ef_use_resolved f with Some _ => true | None => false end))
     (GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) (prog_expr_facts fact_program))
  = Some (Some (TFloat F64), Some (TFloat F64), Some (5%Z, 1%positive), true).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the COMPLETE exact [ExprFact] of the outer argument — the full [CITyped] status (its proof-carrying float64
   TypedConst carrying the exact rational 5/1 and its once-rounded canonical runtime) and the exact resolved
   constant.  Any DIFFERENT resolved float64 value fails this equation. *)
Theorem fact_program_outer_fact :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) (prog_expr_facts fact_program)
  = Some {| ef_const_status :=
              CITyped (TFloat F64)
                (TCFloat F64
                   {| tfc_exact := {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |};
                      tfc_runtime := {| fv_sf := SpecFloat.S754_finite false 5629499534213120 (-50);
                                        fv_ok := const_runtime_canonical F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |} |};
                      tfc_coh := eq_refl;
                      tfc_shape := const_runtime_shape F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |}
                                     {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |} eq_refl |}) ;
            ef_use_resolved :=
              Some (pack_resolved (TFloat F64)
                      (TCFloat F64
                         {| tfc_exact := {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |};
                            tfc_runtime := {| fv_sf := SpecFloat.S754_finite false 5629499534213120 (-50);
                                              fv_ok := const_runtime_canonical F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |} |};
                            tfc_coh := eq_refl;
                            tfc_shape := const_runtime_shape F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |}
                                           {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |} eq_refl |})) |}.
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** ---- §22.16 — REPEATED EQUAL LITERALS [println(1, 1)] are NOT deduplicated: the fact table is keyed by
    OCCURRENCE identity (NodeKey), so two references with DISTINCT keys carry independent facts — each query
    projects its OWN occurrence's exact fact, even when the two expressions are syntactically equal. ---- *)
Definition dup_lit_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt 1; EInt 1 ] ] ].
Example dup_lit_ok : prog_ok dup_lit_program = true. Proof. vm_compute. reflexivity. Qed.

(* the EXACT fact enumeration: TWO entries at DISTINCT keys (local 5 and local 6) with EQUAL fact values (both
   the untyped [1] resolving to [int(1)]).  Same syntax, two occurrences, two entries — the table is keyed by
   occurrence identity, so equal literals are NOT deduplicated by value. *)
Theorem dup_lit_facts_exact :
  GoIndex.NodeKeyMapBase.elements (prog_expr_facts dup_lit_program)
  = [ (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive,
        mkExprFact (CIUntyped (CInt 1)) (Some (pack_resolved (TInteger IInt) (TCInteger IInt 1 eq_refl))))
    ; (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive,
        mkExprFact (CIUntyped (CInt 1)) (Some (pack_resolved (TInteger IInt) (TCInteger IInt 1 eq_refl)))) ].
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** ---- §22.1-22.7 — SINGLE-FAILURE SCARS: each concrete rejected program yields EXACTLY ONE diagnostic with
    the required code, primary anchor (the failing literal/conversion at local 5), and target payload. ---- *)

(* §22.1 default integer overflow: a bare [int_max+1] literal cannot default to [TInteger IInt]. *)
Definition over_default_int_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EInt 9223372036854775808 ] ] ].
Theorem over_default_int_erased :
  erased_report over_default_int_program (GoIndex.Snap.index_program over_default_int_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.2 default float overflow: a bare finite decimal outside finite [float64]. *)
Definition over_default_float_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EFloat (mkDecimal 1 400 eq_refl) ] ] ].
Theorem over_default_float_erased :
  erased_report over_default_float_program (GoIndex.Snap.index_program over_default_float_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TFloat F64)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.3 default complex overflow: a bare complex whose component cannot default to [complex128]. *)
Definition over_default_complex_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EComplex (mkDC (mkDecimal 1 400 eq_refl) (mkDecimal 0 0 eq_refl)) ] ] ].
Theorem over_default_complex_erased :
  erased_report over_default_complex_program (GoIndex.Snap.index_program over_default_complex_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TComplex C128)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.4 invalid explicit integer conversion [int8(128)]: anchored at the conversion, target [TInteger IInt8]. *)
Definition bad_int8_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt8 (EInt 128) ] ] ].
Theorem bad_int8_erased :
  erased_report bad_int8_program (GoIndex.Snap.index_program bad_int8_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.5 fractional float -> integer [int(3.5)]: anchored at the conversion. *)
Definition frac_f2i_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ].
Theorem frac_f2i_erased :
  erased_report frac_f2i_program (GoIndex.Snap.index_program frac_f2i_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.6 nonzero-imaginary complex -> scalar [int(complex(3,1))]: anchored at the conversion. *)
Definition nz_c2s_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 1 0 eq_refl))) ] ] ].
Theorem nz_c2s_erased :
  erased_report nz_c2s_program (GoIndex.Snap.index_program nz_c2s_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* §22.7 wrong-kind conversion [int(true)]: anchored at the conversion, no generic unlocated typing error. *)
Definition wrongkind_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt (EBool true) ] ] ].
Theorem wrongkind_erased :
  erased_report wrongkind_program (GoIndex.Snap.index_program wrongkind_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ---- §22.10 — DUPLICATE MAINS ACROSS FILES: two root-package files each declaring `main`.  The report names
    the CANONICAL later main (path order: [b.go] after [a.go]) as primary, related to the FIRST canonical main
    ([a.go]); construction/insertion order does not change this (both files' mains are at local 3). ---- *)
Theorem dup_across_files_erased :
  option_map (fun p => erased_report_src (prog_files p))
             (build_program c3_ms [ main_file_node (mkFP "a.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
                                  ; main_file_node (mkFP "b.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ] ])
  = Some [ mkErasedDiagnostic DCDuplicateMain (EANode (GoIndex.mkKey (mkFP "b.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "a.go" eq_refl) 3%positive) ] None ].
Proof. vm_compute. reflexivity. Qed.

(** ---- §22.14 — MULTIPLE SIMULTANEOUS FAILURES: two invalid expressions in DIFFERENT files ([a/x.go]'s
    [int8(128)] and [b/y.go]'s [int(3.5)]), one duplicate-main package ([c]), and one missing-main package
    ([d]).  The whole erased report is EXACTLY these four diagnostics in CANONICAL order — expression scars by
    file path first ([a/x.go], [b/y.go]), then package diagnostics by package key ([c] duplicate, [d] missing).
    Construction order does not affect the result. ---- *)
Theorem simultaneous_failures_erased :
  option_map (fun p => erased_report_src (prog_files p))
     (build_program c3_ms
        [ main_file_node (mkFP "a/x.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt8 (EInt 128) ] ] ]
        ; main_file_node (mkFP "b/y.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ]
        ; main_file_node (mkFP "c/p.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
        ; main_file_node (mkFP "c/q.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ]
        ; main_file_node (mkFP "d/z.go" eq_refl) [ ] ])
  = Some [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "a/x.go" eq_refl) 5%positive)) [] (Some (TInteger IInt8))
         ; mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "b/y.go" eq_refl) 5%positive)) [] (Some (TInteger IInt))
         ; mkErasedDiagnostic DCDuplicateMain (EANode (GoIndex.mkKey (mkFP "c/q.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "c/p.go" eq_refl) 3%positive) ] None
         ; mkErasedDiagnostic DCMissingMain (EAPackage "d") [] None ].
Proof. vm_compute. reflexivity. Qed.

(** ---- §16 — MIXED NODE-PRIMARY ORDER: a duplicate-main in package [a] (a later-discovered node diagnostic)
    and an invalid-conversion in package [z] (an earlier-discovered expression diagnostic).  The canonical
    report orders BOTH node-primary diagnostics by NodeKey — the duplicate-main at [a/q.go:3] precedes the
    invalid-conversion at [z/main.go:5] (path [a] < [z]) — NOT by discovery phase (which would put the
    expression scar first).  This is the §16 NodeKeyMap-canonical order the naive `expr ++ pkg` violated. ---- *)
Theorem mixed_order_erased :
  option_map (fun p => erased_report_src (prog_files p))
     (build_program c3_ms
        [ main_file_node (mkFP "a/p.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
        ; main_file_node (mkFP "a/q.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ]
        ; main_file_node (mkFP "z/main.go" eq_refl) [ DMain [ SPrintln [ EIntConvert IInt8 (EInt 128) ] ] ] ])
  = Some [ mkErasedDiagnostic DCDuplicateMain (EANode (GoIndex.mkKey (mkFP "a/q.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "a/p.go" eq_refl) 3%positive) ] None
         ; mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "z/main.go" eq_refl) 5%positive))
             [] (Some (TInteger IInt8)) ].
Proof. vm_compute. reflexivity. Qed.
