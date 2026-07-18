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

(* ============================================================================================================
   §14 (C3) — SINGLE BOTTOM-UP PASS.  [occ_statuses me e] computes the [const_info] of EVERY sub-occurrence of
   [e] (keyed by its canonical local id, matching [occs_expr]) in ONE pass, each node's status derived from its
   ONE child's already-computed status via [const_info_step] (never re-descending a subtree).  It is proved
   EQUAL to the per-node [const_info] specification [statuses_spec], so the analysis reads each occurrence's
   status in O(1) — no recursive [const_info] rescan per occurrence.
   ============================================================================================================ *)

Definition hd_status (l : list (positive * option ConstInfo)) : option ConstInfo :=
  match l with (_, cs) :: _ => cs | [] => None end.

Fixpoint occ_statuses (me : positive) (e : GoExpr) : list (positive * option ConstInfo) :=
  match e with
  | EIntConvert _ x     => let subs := occ_statuses (Pos.succ me) x in (me, const_info_step e (hd_status subs)) :: subs
  | EFloatConvert _ x   => let subs := occ_statuses (Pos.succ me) x in (me, const_info_step e (hd_status subs)) :: subs
  | EComplexConvert _ x => let subs := occ_statuses (Pos.succ me) x in (me, const_info_step e (hd_status subs)) :: subs
  | _ => [(me, const_info_step e None)]
  end.

(* the per-node SPECIFICATION: each occurrence's status is its subexpression's [const_info] (the existing
   recursive authority), one entry per occurrence in canonical [occs_expr] order. *)
Fixpoint statuses_spec (me : positive) (e : GoExpr) : list (positive * option ConstInfo) :=
  match e with
  | EIntConvert _ x     => (me, const_info e) :: statuses_spec (Pos.succ me) x
  | EFloatConvert _ x   => (me, const_info e) :: statuses_spec (Pos.succ me) x
  | EComplexConvert _ x => (me, const_info e) :: statuses_spec (Pos.succ me) x
  | _ => [(me, const_info e)]
  end.

Lemma hd_status_spec : forall me e, hd_status (statuses_spec me e) = const_info e.
Proof. intros me e; destruct e; reflexivity. Qed.

(** the single bottom-up [const_info_step] pass computes EXACTLY the per-node [const_info] — the impl equals
    the spec, so no per-occurrence recursion is needed to obtain any occurrence's status. *)
Lemma occ_statuses_spec : forall e me, occ_statuses me e = statuses_spec me e.
Proof.
  intros e; induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ]; intro me;
    try reflexivity;
    (cbn [occ_statuses statuses_spec]; rewrite !(IHx (Pos.succ me)); do 2 f_equal;
     rewrite hd_status_spec; symmetry; apply const_info_step_reflect).
Qed.

(** hence each entry carries its subexpression's exact [const_info] (the head is the whole node's). *)
Lemma occ_statuses_head : forall me e, hd_status (occ_statuses me e) = const_info e.
Proof. intros me e. rewrite occ_statuses_spec. apply hd_status_spec. Qed.

(* ---- lift the single pass to the whole file, matching [occs_file]'s expression occurrences ---- *)

(* the per-node [const_info] SPEC over an occurrence stream: keep each EXPRESSION occurrence's (id, const_info),
   drop non-expression occurrences (file / package clause / statement / declaration have no const status). *)
Definition expr_statuses_of_occs (l : list (positive * GoIndex.SourceOccurrence)) : list (positive * option ConstInfo) :=
  fold_right (fun idocc acc =>
    match GoIndex.view_expr (snd idocc) with
    | Some e => (fst idocc, const_info e) :: acc
    | None => acc
    end) [] l.

Lemma expr_statuses_of_occs_cons : forall x l,
  expr_statuses_of_occs (x :: l)
  = match GoIndex.view_expr (snd x) with
    | Some e => (fst x, const_info e) :: expr_statuses_of_occs l
    | None => expr_statuses_of_occs l end.
Proof. reflexivity. Qed.

Lemma expr_statuses_of_occs_app : forall a b,
  expr_statuses_of_occs (a ++ b) = expr_statuses_of_occs a ++ expr_statuses_of_occs b.
Proof.
  induction a as [|x a IH]; intro b; [reflexivity|].
  rewrite <- app_comm_cons, !expr_statuses_of_occs_cons, IH.
  destruct (GoIndex.view_expr (snd x)); reflexivity.
Qed.

(* the single-pass expression status list mirrors [occs_expr]'s (all-expression) occurrences exactly. *)
Lemma statuses_spec_expr_occs : forall e parent role me,
  statuses_spec me e = expr_statuses_of_occs (GoIndex.occs_expr parent role me e).
Proof.
  induction e as [ b|n1|n2|s| it x IHx | df | ft x IHx | dcx | ct x IHx ]; intros parent role me;
    try reflexivity;
    (cbn [statuses_spec GoIndex.occs_expr expr_statuses_of_occs GoIndex.view_expr GoIndex.occurrence_view snd fst];
     rewrite (IHx me GoIndex.RConversionOperand (Pos.succ me)); reflexivity).
Qed.

(* the whole-file single pass, mirroring [occs_file] (statements / declarations contribute only their args). *)
Fixpoint status_args (me : positive) (es : list GoExpr) : list (positive * option ConstInfo) :=
  match es with
  | [] => []
  | e :: rest => occ_statuses me e ++ status_args (Pos.succ (GoIndex.end_expr me e)) rest
  end.
Definition status_stmt (me : positive) (s : GoStmt) : list (positive * option ConstInfo) :=
  match s with SPrintln args => status_args (Pos.succ me) args end.
Fixpoint status_stmts (me : positive) (ss : list GoStmt) : list (positive * option ConstInfo) :=
  match ss with
  | [] => []
  | s :: rest => status_stmt me s ++ status_stmts (Pos.succ (GoIndex.end_stmt me s)) rest
  end.
Definition status_decl (me : positive) (d : GoDecl) : list (positive * option ConstInfo) :=
  match d with DMain body => status_stmts (Pos.succ me) body end.
Fixpoint status_decls (me : positive) (ds : list GoDecl) : list (positive * option ConstInfo) :=
  match ds with
  | [] => []
  | d :: rest => status_decl me d ++ status_decls (Pos.succ (GoIndex.end_decl me d)) rest
  end.
Definition file_statuses (f : GoSourceFile) : list (positive * option ConstInfo) :=
  status_decls (Pos.succ GoIndex.pkg_id) (source_decls f).

Lemma status_args_occs : forall es parent aidx me,
  status_args me es = expr_statuses_of_occs (GoIndex.occs_args parent aidx me es).
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [status_args GoIndex.occs_args]. rewrite expr_statuses_of_occs_app. f_equal.
  - unfold GoIndex.occs_arg. rewrite occ_statuses_spec. apply statuses_spec_expr_occs.
  - apply IH.
Qed.

Lemma status_stmt_occs : forall s parent sidx me,
  status_stmt me s = expr_statuses_of_occs (GoIndex.occs_stmt parent sidx me s).
Proof.
  intros [args] parent sidx me.
  cbn [status_stmt GoIndex.occs_stmt expr_statuses_of_occs GoIndex.view_expr GoIndex.occurrence_view snd].
  apply status_args_occs.
Qed.

Lemma status_stmts_occs : forall ss parent sidx me,
  status_stmts me ss = expr_statuses_of_occs (GoIndex.occs_stmts parent sidx me ss).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [status_stmts GoIndex.occs_stmts]. rewrite expr_statuses_of_occs_app. f_equal;
    [ apply status_stmt_occs | apply IH ].
Qed.

Lemma status_decl_occs : forall d parent didx me,
  status_decl me d = expr_statuses_of_occs (GoIndex.occs_decl parent didx me d).
Proof.
  intros [body] parent didx me.
  cbn [status_decl GoIndex.occs_decl expr_statuses_of_occs GoIndex.view_expr GoIndex.occurrence_view snd].
  apply status_stmts_occs.
Qed.

Lemma status_decls_occs : forall ds parent didx me,
  status_decls me ds = expr_statuses_of_occs (GoIndex.occs_decls parent didx me ds).
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [status_decls GoIndex.occs_decls]. rewrite expr_statuses_of_occs_app. f_equal;
    [ apply status_decl_occs | apply IH ].
Qed.

(** the file's single-pass statuses ARE the per-node [const_info] of its expression occurrences (IMPL = SPEC). *)
Lemma file_statuses_occs : forall f, file_statuses f = expr_statuses_of_occs (GoIndex.occs_file f).
Proof.
  intro f. unfold file_statuses, GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  cbn [expr_statuses_of_occs GoIndex.view_expr GoIndex.occurrence_view snd].
  apply status_decls_occs.
Qed.

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

(* [prog_expr_facts] is defined below as the SINGLE-PASS fold reading [prog_status_map] (no per-occurrence
   [const_info]); [add_occ_fact] above is its per-node SPECIFICATION, used only to state exactness. *)

(* ============================================================================================================
   §14 (C3) — the OCCURRENCE-KEYED STATUS MAP.  A standard NodeKey map holding EACH expression occurrence's
   [const_info], populated from the whole-file SINGLE PASS ([file_statuses], no per-occurrence rescan) keyed by
   the index's canonical NodeKey.  Its find at a visited occurrence's key is EXACTLY that occurrence's
   [const_info] — so the fact/diagnostic pass reads a status in O(1) instead of recomputing [const_info].
   ============================================================================================================ *)

(* an expression occurrence contributes its (id, const_info view) to the per-node status list. *)
Lemma expr_statuses_of_occs_in : forall l id occ e,
  In (id, occ) l -> GoIndex.view_expr occ = Some e -> In (id, const_info e) (expr_statuses_of_occs l).
Proof.
  induction l as [|[id0 occ0] rest IH]; intros id occ e Hin Hv; [destruct Hin|].
  rewrite expr_statuses_of_occs_cons; cbn [fst snd]. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. rewrite Hv. left; reflexivity.
  - destruct (GoIndex.view_expr occ0); [ right | ]; apply (IH id occ e Hin Hv).
Qed.

Lemma expr_statuses_fst_sub : forall l id,
  In id (map fst (expr_statuses_of_occs l)) -> In id (map fst l).
Proof.
  induction l as [|[id0 occ0] rest IH]; intros id Hin; [exact Hin|].
  rewrite expr_statuses_of_occs_cons in Hin; cbn [fst snd] in *.
  destruct (GoIndex.view_expr occ0) as [e|]; cbn [map fst] in Hin.
  - destruct Hin as [->|Hin]; [left; reflexivity | right; apply IH; exact Hin].
  - right; apply IH; exact Hin.
Qed.

Lemma nodup_expr_statuses : forall l,
  NoDup (map fst l) -> NoDup (map fst (expr_statuses_of_occs l)).
Proof.
  induction l as [|[id occ] rest IH]; intro Hnd; [constructor|].
  cbn [map fst] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  rewrite expr_statuses_of_occs_cons; cbn [fst snd]. destruct (GoIndex.view_expr occ) as [e|].
  - cbn [map fst]. constructor; [ intro Hin; apply Hni, expr_statuses_fst_sub; exact Hin | apply IH; exact Hnd' ].
  - apply IH; exact Hnd'.
Qed.

Definition binding_statuses (b : FilePath * GoSourceFile) : list (GoIndex.NodeKey * option ConstInfo) :=
  map (fun idst => (GoIndex.mkKey (fst b) (fst idst), snd idst)) (file_statuses (snd b)).

Definition status_kvs (p : GoProgram) : list (GoIndex.NodeKey * option ConstInfo) :=
  flat_map binding_statuses (GoAST.file_bindings (prog_files p)).

Definition prog_status_map (p : GoProgram) : GoIndex.NodeKeyMapBase.t (option ConstInfo) :=
  fold_right (fun kv m => GoIndex.NodeKeyMapBase.add (fst kv) (snd kv) m)
    (GoIndex.NodeKeyMapBase.empty (option ConstInfo)) (status_kvs p).

Lemma fold_kv_find {A} (l : list (GoIndex.NodeKey * A)) k v :
  NoDup (map fst l) -> In (k, v) l ->
  GoIndex.NodeKeyMapBase.find k
    (fold_right (fun kv m => GoIndex.NodeKeyMapBase.add (fst kv) (snd kv) m) (GoIndex.NodeKeyMapBase.empty A) l) = Some v.
Proof.
  induction l as [|[k0 v0] rest IH]; intros Hnd Hin; [destruct Hin|].
  cbn [map fst] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  cbn [fold_right fst snd]. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. rewrite GoIndex.nodekeymap_add_eq. reflexivity.
  - assert (Hk : k <> k0).
    { intro He. apply Hni. subst k0. apply in_map_iff. exists (k, v). split; [reflexivity | exact Hin]. }
    rewrite GoIndex.nodekeymap_add_neq by (intro He; apply Hk; symmetry; exact He).
    exact (IH Hnd' Hin).
Qed.

Lemma binding_statuses_fst_file : forall b k,
  In k (map fst (binding_statuses b)) -> GoIndex.nk_file k = fst b.
Proof.
  intros b k Hin. unfold binding_statuses in Hin. rewrite map_map in Hin; cbn [fst] in Hin.
  apply in_map_iff in Hin. destruct Hin as [idst [Hk _]]. subst k. reflexivity.
Qed.

Lemma binding_statuses_nodup : forall b, NoDup (map fst (binding_statuses b)).
Proof.
  intro b. unfold binding_statuses. rewrite map_map; cbn [fst].
  rewrite <- (map_map (@fst positive (option ConstInfo)) (GoIndex.mkKey (fst b))).
  apply NoDup_map_inj; [ intros x y H; injection H as H; exact H |].
  rewrite file_statuses_occs. apply nodup_expr_statuses. apply GoIndex.occs_file_nodup.
Qed.

Lemma status_kvs_nodup (p : GoProgram) : NoDup (map fst (status_kvs p)).
Proof.
  unfold status_kvs. rewrite map_flat_map.
  apply (nodup_flat_map_tag (fun b => map fst (binding_statuses b)) GoIndex.nk_file (fun b => fst b)
           (GoAST.file_bindings (prog_files p))).
  - intros b _. apply binding_statuses_nodup.
  - intros b k _ Hin. apply binding_statuses_fst_file; exact Hin.
  - apply GoAST.file_bindings_nodup_keys.
Qed.

Lemma status_kvs_in (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  In (GoIndex.Snap.node_ref_key r, const_info e) (status_kvs p).
Proof.
  intros Hin Hv. unfold prog_visit in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold status_kvs. apply in_flat_map. exists b. split; [exact Hb|].
  unfold binding_visit in Hrb.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc_at : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc_at.
  assert (Hfs : In (GoIndex.Snap.node_ref_local r, const_info e) (file_statuses (GoIndex.Snap.file_ref_source fr))).
  { rewrite file_statuses_occs. exact (expr_statuses_of_occs_in _ _ occ e Hsrc_at Hv). }
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr' [Hfop' [Hpath' Hsrc']]].
  rewrite Ef in Hfop'. injection Hfop' as <-.
  unfold binding_statuses. apply in_map_iff.
  exists (GoIndex.Snap.node_ref_local r, const_info e). split; cbn [fst snd].
  - rewrite GoIndex.Snap.node_ref_key_eq, Hfile, Hpath'. reflexivity.
  - rewrite <- Hsrc'; exact Hfs.
Qed.

(** STATUS-MAP EXACTNESS: at each visited expression occurrence's key, the status map holds exactly that
    occurrence's [const_info] (obtained from ONE structural pass — no per-occurrence [const_info] rescan). *)
Lemma prog_status_map_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_status_map p) = Some (const_info e).
Proof.
  intros Hin Hv. unfold prog_status_map.
  apply fold_kv_find; [ apply status_kvs_nodup | exact (status_kvs_in p r occ e Hin Hv) ].
Qed.

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

(** the OPERAND of a visited conversion contributes its [const_info] to [status_kvs] at the operand key. *)
Lemma status_kvs_in_operand (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
  In (GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (GoIndex.Snap.node_ref_local r)), const_info x)
     (status_kvs p).
Proof.
  intros Hin Hv Hc. unfold prog_visit in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold status_kvs. apply in_flat_map. exists b. split; [exact Hb|].
  unfold binding_visit in Hrb.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc_at : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc_at.
  destruct (occs_file_operand (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ e x Hsrc_at Hv Hc)
    as [occ' [Hin' Hv']].
  assert (Hfs : In (Pos.succ (GoIndex.Snap.node_ref_local r), const_info x) (file_statuses (GoIndex.Snap.file_ref_source fr))).
  { rewrite file_statuses_occs. exact (expr_statuses_of_occs_in _ _ occ' x Hin' Hv'). }
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr' [Hfop' [Hpath' Hsrc']]].
  rewrite Ef in Hfop'. injection Hfop' as <-.
  unfold binding_statuses. apply in_map_iff.
  exists (Pos.succ (GoIndex.Snap.node_ref_local r), const_info x). split; cbn [fst snd].
  - rewrite GoIndex.Snap.node_ref_key_eq; cbn [GoIndex.nk_file]. rewrite Hfile, Hpath'. reflexivity.
  - rewrite <- Hsrc'; exact Hfs.
Qed.

(** STATUS-MAP OPERAND EXACTNESS: the operand key of a visited conversion holds the operand's exact
    [const_info] — so [local_conv_failure]'s operand status is a map read, not a subtree rescan. *)
Lemma prog_status_map_find_operand (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ e x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
  GoIndex.NodeKeyMapBase.find
    (GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (GoIndex.Snap.node_ref_local r)))
    (prog_status_map p) = Some (const_info x).
Proof.
  intros Hin Hv Hc. unfold prog_status_map.
  apply fold_kv_find; [ apply status_kvs_nodup | exact (status_kvs_in_operand p r occ e x Hin Hv Hc) ].
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

(** the diagnostic(s) an occurrence emits (a singleton or nothing), anchored at its OWN validated ExprRef. *)
Definition occ_expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : list (DiagnosticReason p) :=
  match GoIndex.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match GoIndex.view_expr (snd ro) with
      | None => []
      | Some e =>
          match local_conv_failure e with
          | Some (t, ci) => [ DRInvalidConversion er [] t ci ]
          | None =>
              match arg_default_failure (snd ro) e with
              | Some (c, dt) => [ DRDefaultNotRepresentable er c dt ]
              | None => []
              end
          end
      end
  end.

(* ---- the SINGLE-PASS diagnostic step: reads each occurrence's own status and (for a conversion) its
   OPERAND's status from the precomputed [prog_status_map] — never recomputing [const_info].  Proved to agree
   with the [occ_expr_diags] specification on the visit stream. ---- *)

Definition operand_key {p} (r : GoIndex.Snap.NodeRef p) : GoIndex.NodeKey :=
  GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (GoIndex.Snap.node_ref_local r)).

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
    (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  : list (DiagnosticReason p) :=
  match GoIndex.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match local_conv_failure_sm smap ro with
      | Some (t, ci) => [ DRInvalidConversion er [] t ci ]
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
  intros Hin Hv. unfold local_conv_failure_sm, local_conv_failure, operand_key; cbn [fst snd]; rewrite Hv.
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

Lemma occ_expr_diags_sm_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :
  In ro (prog_visit p) -> occ_expr_diags_sm (prog_status_map p) idx ro = occ_expr_diags idx ro.
Proof.
  intro Hin. destruct ro as [r occ]. unfold occ_expr_diags_sm, occ_expr_diags; cbn [fst snd].
  destruct (GoIndex.as_expr idx r) as [er|] eqn:Ea; [|reflexivity].
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
  { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
    destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [He|]; [exact He|discriminate Ea]. }
  assert (Hocc : occ = GoIndex.Snap.source_occurrence_of_ref r).
  { pose proof Hin as HinC. unfold prog_visit in HinC. apply in_flat_map in HinC. destruct HinC as [b [_ Hrb]].
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

(* the production expression diagnostics: the SINGLE-PASS step over the visit stream (status-map reads). *)
Definition expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  flat_map (occ_expr_diags_sm (prog_status_map p) idx) (prog_visit p).

Lemma expr_diags_eq_spec {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  expr_diags idx = flat_map (occ_expr_diags idx) (prog_visit p).
Proof. unfold expr_diags. apply flat_map_ext_in. intros ro Hin. apply occ_expr_diags_sm_eq; exact Hin. Qed.

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
  unfold prog_visit. rewrite forallb_flat_map. unfold program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_emits, Hsrc. reflexivity.
Qed.

(** every program-visited occurrence IS its reference's exact source occurrence. *)
Lemma prog_visit_view (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) -> occ = GoIndex.Snap.source_occurrence_of_ref r.
Proof.
  unfold prog_visit. intro Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hin]].
  unfold binding_visit in Hin. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _]. exact Hocc.
Qed.

(** per-occurrence: the emitted diagnostics are empty IFF the occurrence emits nothing (pure). *)
Lemma occ_expr_diags_empty {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  (occ_expr_diags idx (r, occ) = nil <-> occ_emits_none_pure occ = true).
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
  rewrite !forallb_forall. split; intros H [r occ] Hin.
  - cbn [snd]. apply (occ_expr_diags_empty idx r occ Hin).
    specialize (H (r, occ) Hin). destruct (occ_expr_diags idx (r, occ)); [reflexivity | discriminate H].
  - specialize (H (r, occ) Hin). cbn [snd] in H.
    apply (occ_expr_diags_empty idx r occ Hin) in H. rewrite H. reflexivity.
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

(* ---- the per-file main-ref bucket: the DeclRefs of a file's decl occurrences, in canonical stream order. ---- *)

Definition file_main_refs {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p)
  : list (GoIndex.DeclRef p) :=
  fold_right (fun (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (acc : list (GoIndex.DeclRef p)) =>
    match GoIndex.as_decl idx (fst ro) with Some dr => dr :: acc | None => acc end)
    [] (GoIndex.Snap.visit_file fr).

(** GENERIC: if each occurrence's DeclRef-mint agrees with its [decl_kind_count] (1 when minted, 0 otherwise),
    the collected bucket's length is the [decl_count_list]. *)
Lemma decl_collect_length_gen {p} (idx : GoIndex.Snap.SyntaxIndex p)
  (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  (forall ro, In ro l -> match GoIndex.as_decl idx (fst ro) with
                         | Some _ => decl_kind_count (snd ro) = 1%nat
                         | None => decl_kind_count (snd ro) = 0%nat end) ->
  length (fold_right (fun ro acc =>
            match GoIndex.as_decl idx (fst ro) with Some dr => dr :: acc | None => acc end) [] l)
  = decl_count_list l.
Proof.
  induction l as [|ro l IH]; intros Hall; [reflexivity|].
  rewrite (decl_count_list_cons ro l). cbn [fold_right].
  pose proof (Hall ro (or_introl eq_refl)) as Hro.
  assert (Hrest : forall x, In x l -> match GoIndex.as_decl idx (fst x) with
             | Some _ => decl_kind_count (snd x) = 1%nat | None => decl_kind_count (snd x) = 0%nat end)
    by (intros x Hx; apply Hall; right; exact Hx).
  destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - cbn [length]. rewrite (IH Hrest), Hro. reflexivity.
  - rewrite (IH Hrest), Hro. reflexivity.
Qed.

(** the per-element count contribution of the DeclRef collector is EXACTLY the occurrence's [decl_kind_count]:
    a DeclRef is minted iff the node's KIND is KTopLevelDecl, which (for a visited occurrence) is its kind. *)
Lemma file_main_refs_length_decl_count {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  length (file_main_refs idx fr) = decl_count_list (GoIndex.Snap.visit_file fr).
Proof.
  unfold file_main_refs. apply decl_collect_length_gen.
  intros [r occ] Hin. cbn [fst snd].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _].
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.occurrence_kind occ).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx r), Hocc. reflexivity. }
  unfold GoIndex.as_decl, GoIndex.as_kind, decl_kind_count.
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KTopLevelDecl) as [He|Hne].
  - rewrite Hk in He. rewrite He. reflexivity.
  - rewrite Hk in Hne. destruct (GoIndex.occurrence_kind occ); try reflexivity. exfalso; apply Hne; reflexivity.
Qed.

(** the per-file bucket length IS the declarative [file_main_count] (via the coherence + the [snd]-only counts). *)
Lemma file_main_refs_length {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  length (file_main_refs idx fr) = file_main_count (source_decls (GoIndex.Snap.file_ref_source fr)).
Proof.
  rewrite file_main_refs_length_decl_count.
  rewrite (decl_count_list_snd (GoIndex.Snap.visit_file fr) (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr))
             (GoIndex.Snap.visit_file_snd p fr)).
  rewrite decl_count_sum_main_file. apply sum_main_file.
Qed.

(* ---- the WHOLE-PROGRAM package main-ref buckets: aggregate the per-file DeclRefs by package (parent dir),
   in canonical FileMap-path order, using reversed accumulation + one final [PM.map rev] (linear, no quadratic
   append; a package entry is created the first time one of its files is visited, even with zero mains). ---- *)

Definition binding_main_refs {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile)
  : list (GoIndex.DeclRef p) :=
  match GoIndex.Snap.file_of_path p (fst b) with
  | Some fr => file_main_refs idx fr
  | None => []
  end.

Definition olen {A} (o : option (list A)) : nat := match o with Some l => length l | None => 0%nat end.

Definition mref_step {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile)
    (acc : PM.t (list (GoIndex.DeclRef p))) : PM.t (list (GoIndex.DeclRef p)) :=
  PM.add (fp_parent (fst b))
         (rev (binding_main_refs idx b) ++ match PM.find (fp_parent (fst b)) acc with Some l => l | None => [] end)
         acc.

Definition package_main_refs_rev {p} (idx : GoIndex.Snap.SyntaxIndex p) : PM.t (list (GoIndex.DeclRef p)) :=
  fold_left (fun a b => mref_step idx b a) (GoAST.file_bindings (prog_files p)) (PM.empty _).

Definition package_main_refs {p} (idx : GoIndex.Snap.SyntaxIndex p) : PM.t (list (GoIndex.DeclRef p)) :=
  PM.map (@rev (GoIndex.DeclRef p)) (package_main_refs_rev idx).

(* the per-package DeclRef count spec, parallel to [list_dir_count] but summing bucket lengths. *)
Fixpoint list_dir_reflen {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string)
    (l : list (FilePath * GoSourceFile)) : nat :=
  match l with
  | [] => 0%nat
  | b :: rest =>
      ((if String.eqb (fp_parent (fst b)) dir then length (binding_main_refs idx b) else 0%nat)
       + list_dir_reflen idx dir rest)%nat
  end.

Lemma list_dir_reflen_0 {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  list_dir_mem dir l = false -> list_dir_reflen idx dir l = 0%nat.
Proof.
  intros dir l; induction l as [|b rest IH]; simpl; [reflexivity|].
  unfold list_dir_mem in *; simpl; intro H. apply Bool.orb_false_iff in H as [Hb Hr].
  rewrite Hb; simpl; apply IH; exact Hr.
Qed.

(** each represented file's bucket length is its [file_main_count]; hence the reflen spec equals [list_dir_count]. *)
Lemma binding_main_refs_length {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) :
  In b (GoAST.file_bindings (prog_files p)) ->
  length (binding_main_refs idx b) = file_main_count (source_decls (snd b)).
Proof.
  intro Hb. unfold binding_main_refs.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [_ Hsrc]]].
  rewrite Hfop, file_main_refs_length, Hsrc. reflexivity.
Qed.

Lemma list_dir_reflen_count {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  (forall b, In b l -> length (binding_main_refs idx b) = file_main_count (source_decls (snd b))) ->
  list_dir_reflen idx dir l = list_dir_count dir l.
Proof.
  intros dir l; induction l as [|b rest IH]; intro Hb; simpl; [reflexivity|].
  rewrite (Hb b (or_introl eq_refl)), IH; [reflexivity | intros x Hx; apply Hb; right; exact Hx].
Qed.

(* ---- per-step + cons rewrite helpers (clean, definitional), so the fold proofs avoid inline reduction. ---- *)

Lemma olen_match {A} (o : option (list A)) :
  length (match o with Some l => l | None => [] end) = olen o.
Proof. destruct o; reflexivity. Qed.

Lemma list_dir_mem_cons : forall dir b l,
  list_dir_mem dir (b :: l) = (String.eqb (fp_parent (fst b)) dir || list_dir_mem dir l)%bool.
Proof. reflexivity. Qed.

Lemma list_dir_reflen_cons {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir b l,
  list_dir_reflen idx dir (b :: l)
  = ((if String.eqb (fp_parent (fst b)) dir then length (binding_main_refs idx b) else 0%nat)
     + list_dir_reflen idx dir l)%nat.
Proof. reflexivity. Qed.

Lemma mref_step_find_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) acc dir :
  fp_parent (fst b) = dir ->
  PM.find dir (mref_step idx b acc)
  = Some (rev (binding_main_refs idx b) ++ match PM.find dir acc with Some l => l | None => [] end).
Proof. intro E. unfold mref_step. rewrite E, PMF.add_eq_o by reflexivity. reflexivity. Qed.

Lemma mref_step_find_neq {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) acc dir :
  fp_parent (fst b) <> dir -> PM.find dir (mref_step idx b acc) = PM.find dir acc.
Proof. intro E. unfold mref_step. rewrite PMF.add_neq_o by exact E. reflexivity. Qed.

Lemma mref_step_olen_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) acc dir :
  fp_parent (fst b) = dir ->
  olen (PM.find dir (mref_step idx b acc)) = (length (binding_main_refs idx b) + olen (PM.find dir acc))%nat.
Proof.
  intro E. rewrite (mref_step_find_eq idx b acc dir E). cbn [olen].
  rewrite length_app, length_rev, olen_match. reflexivity.
Qed.

(* the fold LENGTH characterization (mirror of [pkg_foldl_find], tracking bucket lengths). *)
Lemma mref_foldl_olen {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  olen (PM.find dir (fold_left (fun a b => mref_step idx b a) l acc))
  = (if list_dir_mem dir l
     then (list_dir_reflen idx dir l + olen (PM.find dir acc))%nat
     else olen (PM.find dir acc)).
Proof.
  induction l as [|b rest IH]; intros acc dir; [reflexivity|].
  cbn [fold_left]. rewrite (IH (mref_step idx b acc) dir).
  rewrite list_dir_mem_cons, (list_dir_reflen_cons idx dir b rest).
  destruct (String.eqb (fp_parent (fst b)) dir) eqn:E; cbn [orb].
  - apply String.eqb_eq in E. rewrite (mref_step_olen_eq idx b acc dir E).
    destruct (list_dir_mem dir rest) eqn:Erest;
      [ | rewrite (list_dir_reflen_0 idx dir rest Erest) ]; lia.
  - apply String.eqb_neq in E. rewrite (mref_step_find_neq idx b acc dir E). reflexivity.
Qed.

(* the fold PRESENCE characterization: a bucket exists iff a file of that package was visited. *)
Lemma mref_foldl_none {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  PM.find dir (fold_left (fun a b => mref_step idx b a) l acc) = None
  <-> (list_dir_mem dir l = false /\ PM.find dir acc = None).
Proof.
  induction l as [|b rest IH]; intros acc dir;
    [ cbn [fold_left]; split; [ intro H; split; [reflexivity|exact H] | intros [_ H]; exact H ] |].
  cbn [fold_left]. rewrite (IH (mref_step idx b acc) dir), list_dir_mem_cons.
  destruct (String.eqb (fp_parent (fst b)) dir) eqn:E; cbn [orb].
  - apply String.eqb_eq in E. rewrite (mref_step_find_eq idx b acc dir E).
    split; [ intros [_ Hd]; discriminate Hd | intros [Hf _]; discriminate Hf ].
  - apply String.eqb_neq in E. rewrite (mref_step_find_neq idx b acc dir E). tauto.
Qed.

(** BUCKET LENGTH EXACTNESS: a present bucket's length is the package's declarative main count [pkg_main_count]
    (= [ps_main_count]) — the reference collection AGREES with the package count judgment. *)
Lemma package_main_refs_bucket_len {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (package_main_refs idx) = Some l -> length l = pkg_main_count dir (prog_files p).
Proof.
  intros dir l Hfind. unfold package_main_refs in Hfind. rewrite PMF.map_o in Hfind.
  destruct (PM.find dir (package_main_refs_rev idx)) as [l'|] eqn:Erev; cbn [option_map] in Hfind;
    [ injection Hfind as <- | discriminate Hfind ].
  rewrite length_rev.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:Em; [reflexivity|].
    exfalso. assert (Hn : PM.find dir (package_main_refs_rev idx) = None).
    { apply (mref_foldl_none idx). split; [exact Em | apply PMF.empty_o]. }
    rewrite Hn in Erev; discriminate Erev. }
  pose proof (mref_foldl_olen idx (GoAST.file_bindings (prog_files p)) (PM.empty _) dir) as Hol.
  unfold package_main_refs_rev in Erev. rewrite Erev in Hol. cbn [olen] in Hol.
  rewrite Hmem, PMF.empty_o in Hol. cbn [olen] in Hol. rewrite Nat.add_0_r in Hol.
  rewrite Hol, (list_dir_reflen_count idx dir (GoAST.file_bindings (prog_files p))).
  - reflexivity.
  - intros b Hb. apply binding_main_refs_length; exact Hb.
Qed.

(** DOMAIN EXACTNESS: the bucket map's domain is exactly the represented package set (parity with
    [package_summaries]): a bucket is present iff a file has that parent directory. *)
Lemma package_main_refs_present {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir,
  PM.In dir (package_main_refs idx) <-> list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true.
Proof.
  intro dir. unfold package_main_refs. rewrite PMF.map_in_iff. split.
  - intros [l Hmt]. apply PMF.find_mapsto_iff in Hmt.
    destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:Em; [reflexivity|].
    exfalso. assert (Hn : PM.find dir (package_main_refs_rev idx) = None).
    { apply (mref_foldl_none idx). split; [exact Em | apply PMF.empty_o]. }
    rewrite Hn in Hmt; discriminate Hmt.
  - intro Hmem. apply PMF.in_find_iff. intro Hn.
    apply (mref_foldl_none idx) in Hn. destruct Hn as [Hm _]. rewrite Hm in Hmem; discriminate Hmem.
Qed.

(* ---- SUCCESS-side PACKAGE FACTS (§11): on a valid program every present bucket is a SINGLETON (its length
   is the package's main count, which is exactly one), so each package has ONE canonical main [DeclRef]. ---- *)

Lemma package_main_refs_singleton_on_success {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  AllPackagesOneMain p -> forall dir l,
  PM.find dir (package_main_refs idx) = Some l -> exists d, l = [d].
Proof.
  intros Hall dir l Hfind.
  pose proof (package_main_refs_bucket_len idx dir l Hfind) as Hlen.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { apply (package_main_refs_present idx dir). apply PMF.in_find_iff. rewrite Hfind. discriminate. }
  assert (Hmt : PM.MapsTo dir (mkPkgSummary (pkg_main_count dir (prog_files p))) (package_summaries (prog_files p))).
  { apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (Hall dir _ Hmt) as Hone. cbn [ps_main_count] in Hone.
  rewrite Hone in Hlen.
  destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate.
  exists d; reflexivity.
Qed.

(* ---- BELONGS: a main DeclRef in a package's bucket belongs to THAT package (its file's parent = the key) —
   so two singleton main buckets cannot be swapped between packages. ---- *)

Lemma decl_collect_mem {p} (idx : GoIndex.Snap.SyntaxIndex p)
  (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (d : GoIndex.DeclRef p) :
  In d (fold_right (fun ro acc => match GoIndex.as_decl idx (fst ro) with Some dr => dr :: acc | None => acc end) [] l) ->
  exists ro, In ro l /\ GoIndex.as_decl idx (fst ro) = Some d.
Proof.
  induction l as [|ro rest IH]; intro Hin; [destruct Hin|].
  cbn [fold_right] in Hin. destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct Hin as [<-|Hin].
    + exists ro. split; [left; reflexivity | exact Ed].
    + destruct (IH Hin) as [ro' [Hin' Hd]]. exists ro'. split; [right; exact Hin' | exact Hd].
  - destruct (IH Hin) as [ro' [Hin' Hd]]. exists ro'. split; [right; exact Hin' | exact Hd].
Qed.

Lemma file_main_refs_file {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) (d : GoIndex.DeclRef p) :
  In d (file_main_refs idx fr) -> GoIndex.Snap.node_ref_file (GoIndex.erase_ref d) = fr.
Proof.
  intro Hin. unfold file_main_refs in Hin.
  destruct (decl_collect_mem idx (GoIndex.Snap.visit_file fr) d Hin) as [[r occ] [Hro Hd]]. cbn [fst] in Hd.
  rewrite (GoIndex.erase_as_kind idx r GoIndex.KTopLevelDecl d Hd).
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hro) as [_ Hf]. exact Hf.
Qed.

Lemma mref_foldl_mem {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir d,
  In d (match PM.find dir (fold_left (fun a b => mref_step idx b a) l acc) with Some x => x | None => [] end) ->
  (exists b, In b l /\ fp_parent (fst b) = dir /\ In d (binding_main_refs idx b))
  \/ In d (match PM.find dir acc with Some x => x | None => [] end).
Proof.
  induction l as [|b rest IH]; intros acc dir d Hin; [right; exact Hin|].
  cbn [fold_left] in Hin. destruct (IH (mref_step idx b acc) dir d Hin) as [[b' [Hb' [Hp' Hd']]] | Hrest].
  - left. exists b'. split; [right; exact Hb' | split; [exact Hp' | exact Hd']].
  - destruct (string_dec (fp_parent (fst b)) dir) as [He|Hne].
    + rewrite (mref_step_find_eq idx b acc dir He) in Hrest. cbn [option_map] in Hrest.
      apply in_app_or in Hrest. destruct Hrest as [Hd1|Hd2].
      * left. exists b. split; [left; reflexivity | split; [exact He | apply in_rev; exact Hd1]].
      * right. exact Hd2.
    + rewrite (mref_step_find_neq idx b acc dir Hne) in Hrest. right. exact Hrest.
Qed.

Lemma package_main_refs_belongs {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (package_main_refs idx) = Some l ->
  forall d, In d l ->
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref d))) = dir.
Proof.
  intros dir l Hfind d Hin.
  unfold package_main_refs in Hfind. rewrite PMF.map_o in Hfind.
  destruct (PM.find dir (package_main_refs_rev idx)) as [lr|] eqn:Erev; cbn [option_map] in Hfind;
    [ injection Hfind as <- | discriminate Hfind ].
  apply in_rev in Hin.
  assert (Hb : In d (match PM.find dir (package_main_refs_rev idx) with Some x => x | None => [] end))
    by (rewrite Erev; exact Hin).
  unfold package_main_refs_rev in Hb.
  destruct (mref_foldl_mem idx (GoAST.file_bindings (prog_files p)) (PM.empty _) dir d Hb) as [[b [_ [Hp Hd]]] | Hempty].
  - unfold binding_main_refs in Hd. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [| destruct Hd].
    rewrite (file_main_refs_file idx fr d Hd), (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef). exact Hp.
  - rewrite PMF.empty_o in Hempty. destruct Hempty.
Qed.

(* (The per-package main is exposed as [package_main_at] over [CompilationFacts] below — a projection of the
   retained buckets + validity, not a separate [idx]-recomputation.) *)

(* ============================================================================================================
   §8 (C3) — the PACKAGE diagnostics.  Every package with a main count other than one is a failure; the anchor
   is a validated [PackageRef] (each package in [package_summaries] is represented, so the reference is real).
   Emptiness is tied DIRECTLY to [pkg_all_ok] (the package half of the decision).
   (ROOT emits [DRMissingMain] for every non-conforming package; a later refinement distinguishes the duplicate
   case with [DRDuplicateMain] over the collected main [DeclRef]s.)
   ============================================================================================================ *)

Definition bool_sb (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** every package appearing in [package_summaries] names a represented package. *)
Lemma summary_elem_present (p : GoProgram) dir s :
  In (dir, s) (PM.elements (package_summaries (prog_files p))) -> package_present_b p dir = true.
Proof.
  intro Hin. unfold package_present_b.
  assert (Hmt : PM.MapsTo dir s (package_summaries (prog_files p))).
  { apply PMF.elements_mapsto_iff, InA_alt. exists (dir, s). split; [ split; reflexivity | exact Hin ]. }
  destruct (package_no_empty (prog_files p) dir (ex_intro _ s Hmt)) as [b [Hb Hpar]].
  unfold list_dir_mem. apply existsb_exists. exists b. split; [ exact Hb | apply String.eqb_eq; exact Hpar ].
Qed.

(* A non-conforming package is diagnosed with a STRUCTURED reason anchored in the exact snapshot:
   - two or more mains -> [DRDuplicateMain] over the FIRST two canonical main [DeclRef]s of the bucket
     ([later_primary] = the second/first-redundant main; [earlier_related] = the first main);
   - zero mains -> [DRMissingMain] anchored at the validated [PackageRef].
   The canonical bucket order (FileMap-path then local NodeKey) makes the duplicate anchors deterministic;
   evidence is never overwritten (the bucket preserves every main). *)
Definition pkg_diag_of {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : string * PackageSummary)
  : list (DiagnosticReason p) :=
  if Nat.eqb (ps_main_count (snd b)) 1 then []
  else match PM.find (fst b) (package_main_refs idx) with
       | Some (d1 :: d2 :: _) => [ DRDuplicateMain d2 d1 ]
       | _ => match bool_sb (package_present_b p (fst b)) with
              | left H  => [ DRMissingMain (mkPackageRef p (fst b) H) ]
              | right _ => []
              end
       end.

Definition pkg_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  flat_map (pkg_diag_of idx) (PM.elements (package_summaries (prog_files p))).

(** THE PACKAGE COMPLETENESS: no package diagnostic IFF every package has exactly one main ([pkg_all_ok]).
    (A non-conforming package always emits — [DRDuplicateMain] when the bucket has >=2 refs, else
    [DRMissingMain], since a summary element's package is always represented.) *)
Lemma pkg_diags_empty_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) : pkg_diags idx = nil <-> pkg_all_ok p = true.
Proof.
  unfold pkg_diags, pkg_all_ok. rewrite flat_map_nil_forallb.
  assert (Heq : forallb (fun x => match pkg_diag_of idx x with nil => true | _ => false end)
                        (PM.elements (package_summaries (prog_files p)))
              = forallb (fun b => Nat.eqb (ps_main_count (snd b)) 1)
                        (PM.elements (package_summaries (prog_files p)))).
  { apply GoTypes.forallb_ext_in. intros [dir s] Hin. unfold pkg_diag_of. cbn [fst snd].
    destruct (Nat.eqb (ps_main_count s) 1) eqn:E; [ reflexivity |].
    destruct (PM.find dir (package_main_refs idx)) as [[|d1 [|d2 rest]]|] eqn:Eb;
      try reflexivity;
      (destruct (bool_sb (package_present_b p dir)) as [H|H]; [ reflexivity |];
       rewrite (summary_elem_present p dir s Hin) in H; discriminate H). }
  rewrite Heq. reflexivity.
Qed.

(* ============================================================================================================
   §12/§13/§14 (C3) — the ONE retained indexed-analysis root.  [analyze] builds ONE [IndexedProgram] and returns
   either exact facts (on success) or a NONEMPTY structured diagnostic list (on failure).  The success/failure
   decision is the analysis-native [analysis_ok_b] (proved [= GoCompile]); [collect_diagnostics] gives the
   structured failure payload, nonempty exactly when the decision fails.
   ============================================================================================================ *)

Definition collect_diagnostics (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  expr_diags idx ++ pkg_diags idx.

Lemma app_nil_iff {A} (l1 l2 : list A) : l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof. split; [ apply app_eq_nil | intros [-> ->]; reflexivity ]. Qed.

Lemma collect_diagnostics_empty_iff (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  collect_diagnostics p idx = nil <-> analysis_ok_b p = true.
Proof.
  unfold collect_diagnostics. rewrite app_nil_iff, expr_diags_empty_iff, pkg_diags_empty_iff.
  unfold analysis_ok_b. rewrite Bool.andb_true_iff, expr_all_ok_program_typedb. reflexivity.
Qed.

Lemma collect_diagnostics_nonempty (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  analysis_ok_b p = false -> collect_diagnostics p idx <> nil.
Proof.
  intros H Hc. apply (collect_diagnostics_empty_iff p idx) in Hc. rewrite Hc in H. discriminate H.
Qed.

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

Lemma occ_expr_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) ro : forall d,
  In d (occ_expr_diags idx ro) -> diag_is_typing d = true /\ diag_is_package d = false.
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
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [ro [_ Hd]].
  apply (occ_expr_diags_family idx ro d Hd).
Qed.
Lemma expr_diags_not_package {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (expr_diags idx) -> diag_is_package d = false.
Proof.
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [ro [_ Hd]].
  apply (occ_expr_diags_family idx ro d Hd).
Qed.

Lemma pkg_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d,
  In d (pkg_diags idx) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  intros d Hin. unfold pkg_diags in Hin. apply in_flat_map in Hin. destruct Hin as [b [_ Hd]].
  unfold pkg_diag_of in Hd. destruct (Nat.eqb (ps_main_count (snd b)) 1); [destruct Hd|].
  destruct (PM.find (fst b) (package_main_refs idx)) as [[|d1 [|d2 rest]]|].
  - destruct (bool_sb (package_present_b p (fst b))) as [H|H]; [ destruct Hd as [<-|[]]; split; reflexivity | destruct Hd ].
  - destruct (bool_sb (package_present_b p (fst b))) as [H|H]; [ destruct Hd as [<-|[]]; split; reflexivity | destruct Hd ].
  - destruct Hd as [<-|[]]; split; reflexivity.
  - destruct (bool_sb (package_present_b p (fst b))) as [H|H]; [ destruct Hd as [<-|[]]; split; reflexivity | destruct Hd ].
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
  unfold collect_diagnostics. rewrite existsb_app.
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
  unfold collect_diagnostics. rewrite existsb_app.
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

(** §10 — the public expression-fact query, through a TYPED reference (not a raw key): total function returning
    the occurrence's fact if present.  On a valid program every expression reference has an entry. *)
Definition expr_fact_at {p ip} (facts : CompilationFacts p ip) (er : GoIndex.ExprRef p) : option ExprFact :=
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (cf_expr_facts facts)).

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

(** the ONE [CompilationFacts] builder — the SAME occurrence-keyed [ExprFactTable] + package buckets given a
    validity proof.  BOTH [analyze]'s [AnalysisOK] and the witness compilation path use exactly this, so there
    is ONE fact construction (no parallel authority that could disagree; they differ only in the erased
    validity proof). *)
Definition analysis_facts (p : GoProgram) (ip : GoIndex.IndexedProgram p) (H : ProgValid p) : CompilationFacts p ip :=
  mkCompilationFacts (prog_expr_fact_table p ip)
    (package_main_refs (GoIndex.indexed_syntax ip))
    (package_main_refs_present (GoIndex.indexed_syntax ip))
    (package_main_refs_bucket_len (GoIndex.indexed_syntax ip))
    (package_main_refs_belongs (GoIndex.indexed_syntax ip))
    H.

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

(** §14 — the ONE analysis: the DECISION is exactly "the diagnostic pass produced nothing".  On success the
    facts (occurrence-keyed status map + package buckets) are exposed with the derived validity; on failure the
    EXACT diagnostic list is exposed.  No separate accept/reject computation. *)
Definition analyze_indexed (p : GoProgram) (ip : GoIndex.IndexedProgram p) : AnalysisResult p ip :=
  match list_is_nil (collect_diagnostics p (GoIndex.indexed_syntax ip)) with
  | left He  => AnalysisOK (analysis_facts p ip (analyze_valid_of_no_diags p ip He))
  | right Hne => AnalysisFailed (collect_diagnostics p (GoIndex.indexed_syntax ip)) Hne
  end.

Definition analyze (p : GoProgram) : ProgramAnalysis p :=
  let ip := GoIndex.index_program p in
  mkProgramAnalysis ip (analyze_indexed p ip).

(** ANALYSIS EXACTNESS: analysis succeeds (exposes facts) IFF the program is valid ([ProgValid] = [GoCompile]);
    it fails (exposes nonempty diagnostics) IFF the program is invalid.  Success and failure are exclusive. *)
Theorem analyze_ok_iff_ProgValid (p : GoProgram) :
  (exists facts, pa_result (analyze p) = AnalysisOK facts) <-> ProgValid p.
Proof.
  unfold analyze, analyze_indexed; cbn [pa_result].
  destruct (list_is_nil (collect_diagnostics p (GoIndex.indexed_syntax (GoIndex.index_program p)))) as [He|Hne].
  - split; intro Hx; [ apply (analyze_valid_of_no_diags p (GoIndex.index_program p) He) | eexists; reflexivity ].
  - split; intro Hx.
    + destruct Hx as [facts Hf]; discriminate Hf.
    + exfalso. apply Hne, (collect_diagnostics_empty_iff p _), (analysis_ok_b_ProgValid p); exact Hx.
Qed.

Theorem analyze_failed_iff_not_ProgValid (p : GoProgram) :
  (exists ds Hne, pa_result (analyze p) = AnalysisFailed ds Hne) <-> ~ ProgValid p.
Proof.
  unfold analyze, analyze_indexed; cbn [pa_result].
  destruct (list_is_nil (collect_diagnostics p (GoIndex.indexed_syntax (GoIndex.index_program p)))) as [He|Hne].
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
  unfold analyze, analyze_indexed; cbn [pa_result].
  destruct (list_is_nil (collect_diagnostics p (GoIndex.indexed_syntax (GoIndex.index_program p)))) as [He|Hn].
  - intro H; discriminate H.
  - intro H. inversion H. reflexivity.
Qed.

(** [GoCompile p] IS whole-program admissibility: the program is typed through [GoTypes] AND every package
    has exactly one `main`.  The package clause is now SOURCE-owned (each file's [source_package]), rendered
    by [GoRender] — it is no longer a compiler-derived fact, so there is no [cf_pkg_name] / [CompilationFacts]
    record: the compiled evidence is exactly [ProgValid p].  Richer per-program facts (symbol/type tables)
    will decorate this same program later without a second AST; there is no unused placeholder now. *)
Definition GoCompile (p : GoProgram) : Prop := ProgValid p.

(** §16 (C3) — a compiled program RETAINS the whole successful analysis: the program, the SAME
    [IndexedProgram] the analysis ran on, and its [CompilationFacts] (occurrence-keyed facts + package
    buckets + validity).  [cp_ok] is a projection of the retained facts' validity — the compiled evidence is
    NOT constructible from a parallel path (only [analyze]'s [AnalysisOK] facts build it). *)
Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_index   : GoIndex.IndexedProgram cp_program;
  cp_facts   : CompilationFacts cp_program cp_index
}.

Definition cp_ok (cp : CompilableProgram) : GoCompile (cp_program cp) := cf_valid (cp_facts cp).

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

(** §18 — the production compiler PROJECTS the ONE retained [analyze] (a single let-bound [pa]: same index,
    same analysis result).  Success exposes the [CompilableProgram] from [AnalysisOK]; failure CARRIES the
    exact analysis diagnostics — never a second checker or a coarse recomputation. *)
Definition go_compile (p : GoProgram) : CompileOutcome p :=
  let pa := analyze p in
  match pa_result pa with
  | AnalysisOK facts      => CompiledOk (mkCompilable p (pa_indexed pa) facts) eq_refl
  | AnalysisFailed ds Hne => CompileFailed (mkCompileFailure ds Hne)
  end.

(** (A) internal exactness: [go_compile] succeeds exactly on admissible programs, whole-program. *)
Theorem go_compile_ok_valid : forall p cp Hcp,
  go_compile p = CompiledOk cp Hcp -> cp_program cp = p /\ GoCompile (cp_program cp).
Proof.
  intros p cp Hcp Heq. revert Heq. unfold go_compile; cbv zeta.
  destruct (pa_result (analyze p)) as [ facts | ds Hne ]; intro Heq; [| discriminate Heq].
  injection Heq as <-. cbn [cp_program]. split; [ reflexivity | exact (cf_valid facts) ].
Qed.

Theorem go_compile_complete : forall p,
  GoCompile p -> exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p Hvalid. unfold go_compile; cbv zeta.
  destruct (analyze_ok_iff_ProgValid p) as [ _ Hok ].
  destruct (Hok Hvalid) as [ facts Hf ]. rewrite Hf. eexists; eexists; reflexivity.
Qed.

(** fixture helper: acceptance through the theorems. *)
Lemma go_compile_ok_of_prog_ok : forall p, prog_ok p = true -> exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof. intros p H; apply go_compile_complete, (proj1 (prog_ok_iff p)); exact H. Qed.

(** the CHEAP witness builder: the SAME [CompilationFacts] [analyze]'s [AnalysisOK] builds (identical
    [prog_expr_facts] / [package_main_refs] / retained index), with [cp_program] a direct projection so
    rendering never reduces the (opaque, vm-compute-unfriendly) index analysis.  [go_compile]'s success value
    agrees observationally (only the erased validity proof differs) — [go_compile p = CompiledOk cp _ ->
    cp_program cp = p] is the shared observable. *)
Definition compilable_of_valid (p : GoProgram) (H : GoCompile p) : CompilableProgram :=
  mkCompilable p (GoIndex.index_program p) (analysis_facts p (GoIndex.index_program p) H).

(** fixture helper: a non-typed program is REJECTED at the TYPING legacy class — a projection of the carried
    diagnostics, never a [program_typedb] rerun. *)
Lemma go_compile_untyped : forall p, program_typedb p = false -> legacy_compile_class (go_compile p) = LCTyping.
Proof.
  intros p Hf. unfold go_compile; cbv zeta.
  destruct (pa_result (analyze p)) as [ facts | ds Hne ] eqn:E.
  - exfalso. assert (Hv : ProgValid p) by (apply (analyze_ok_iff_ProgValid p); exists facts; exact E).
    pose proof (proj2 (program_typedb_iff p) (proj1 Hv)) as Ht. rewrite Ht in Hf; discriminate Hf.
  - cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (analyze_failed_ds p ds Hne E), existsb_typing_collect, Hf. reflexivity.
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
  intro p. unfold go_compile_class, go_compile; cbv zeta.
  destruct (pa_result (analyze p)) as [facts | ds Hne] eqn:E.
  - assert (Hpv : ProgValid p) by (apply (analyze_ok_iff_ProgValid p); exists facts; exact E).
    cbn [legacy_compile_class]. rewrite (proj2 (prog_ok_iff p) Hpv). reflexivity.
  - assert (Hnv : ~ ProgValid p)
      by (apply (analyze_failed_iff_not_ProgValid p); exists ds; exists Hne; exact E).
    assert (Hpf : prog_ok p = false)
      by (destruct (prog_ok p) eqn:Ep; [ exfalso; apply Hnv, (proj1 (prog_ok_iff p)); exact Ep | reflexivity ]).
    rewrite Hpf. cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (analyze_failed_ds p ds Hne E), existsb_typing_collect, existsb_package_collect.
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
