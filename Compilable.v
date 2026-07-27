(** The exact acceptance model for the pinned one-shot `go build ./...`, as evidence over the one raw program. *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Arith Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Integer Float Complex FilePath ModulePath Collections Syntax Index Typing.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
Open Scope Z_scope.

(** The compiler owns the predeclared context: a conversion's source name resolves to its semantic type here. *)
Definition predeclared_type_of_name (n : Names.TypeName) : Typing.SemanticType :=
  match n with
  | Names.Int    => Typing.IntegerType Integer.Int    | Names.Int8  => Typing.IntegerType Integer.Int8
  | Names.Int16  => Typing.IntegerType Integer.Int16  | Names.Int32 => Typing.IntegerType Integer.Int32
  | Names.Int64  => Typing.IntegerType Integer.Int64
  | Names.Uint   => Typing.IntegerType Integer.Uint   | Names.Uint8  => Typing.IntegerType Integer.Uint8
  | Names.Uint16 => Typing.IntegerType Integer.Uint16 | Names.Uint32 => Typing.IntegerType Integer.Uint32
  | Names.Uint64 => Typing.IntegerType Integer.Uint64
  | Names.Float32 => Typing.FloatType F32 | Names.Float64 => Typing.FloatType F64
  | Names.Complex64 => Typing.ComplexType C64 | Names.Complex128 => Typing.ComplexType C128
  | Names.Byte => Typing.IntegerType Integer.Uint8 | Names.Rune => Typing.IntegerType Integer.Int32
  end.

Definition predeclared_type (ts : Syntax.TypeExpr) : Typing.SemanticType :=
  predeclared_type_of_name (Syntax.type_expr_name ts).

(** These notations fix the resolver, so the production pass and its proofs read against one context. *)
Local Notation constant_info        := (Typing.constant_info predeclared_type) (only parsing).
Local Notation constant_info_step   := (Typing.constant_info_step predeclared_type) (only parsing).
Local Notation resolve_constant := (Typing.resolve_constant predeclared_type) (only parsing).
Local Notation resolve      := (Typing.resolve predeclared_type) (only parsing).
Local Notation expression_typedb       := (Typing.expression_typedb predeclared_type) (only parsing).
Local Notation stmt_typedb       := (Typing.stmt_typedb predeclared_type) (only parsing).
Local Notation decl_typedb       := (Typing.decl_typedb predeclared_type) (only parsing).
Local Notation file_typedb       := (Typing.file_typedb predeclared_type) (only parsing).
Local Notation source_file_typedb := (Typing.source_file_typedb predeclared_type) (only parsing).
Local Notation program_typedb    := (Typing.program_typedb predeclared_type) (only parsing).

(** Static admissibility is typing over the same raw AST, so every println argument must resolve. *)

Definition decl_is_main (d : Syntax.Decl) : bool := match d with Syntax.Main _ => true end.
Definition file_main_count (decls : list Syntax.Decl) : nat := List.length (List.filter decl_is_main decls).

Module PackageMap := Collections.PackageMap.
Module PackageFacts := Collections.PackageFacts.
Module PackageProperties := Collections.PackageProperties.

(** A package summary carries only the live fact the fragment needs: its total `main` count. *)
Record PackageSummary : Type := MakePackageSummary { summary_main_count : nat }.
Definition summary_count (o : option PackageSummary) : nat := match o with Some s => summary_main_count s | None => 0 end.

(** accumulate one file's `main` count into its parent-directory package summary. *)
Definition package_map_add_main (dir : string) (n : nat) (acc : PackageMap.t PackageSummary) : PackageMap.t PackageSummary :=
  PackageMap.add dir (MakePackageSummary (n + summary_count (PackageMap.find dir acc))) acc.
Definition package_step (path : FilePath.T) (sf : Syntax.File) (acc : PackageMap.t PackageSummary) : PackageMap.t PackageSummary :=
  package_map_add_main (FilePath.parent path) (file_main_count (Syntax.declarations sf)) acc.

(** One fold over the file map, each file contributing its count once, rather than a scan per file. *)
Definition package_summaries (fm : Syntax.Files) : PackageMap.t PackageSummary :=
  Syntax.FileMap.fold package_step fm (PackageMap.empty PackageSummary).

(** The one-main reading is a consequence of the current grammar, never a source root of its own. *)
Definition current_grammar_one_main (p : Syntax.Program) : Prop :=
  forall dir s, PackageMap.MapsTo dir s (package_summaries (Syntax.files p)) -> summary_main_count s = 1%nat.

(** The readable index-free specification decision: the two factored package rules as separate roots. *)
Definition package_decls_unique_b (p : Syntax.Program) : bool :=
  forallb (fun b => Nat.leb (summary_main_count (snd b)) 1) (PackageMap.elements (package_summaries (Syntax.files p))).
Definition main_pkgs_have_entry_b (p : Syntax.Program) : bool :=
  forallb (fun b => Nat.leb 1 (summary_main_count (snd b))) (PackageMap.elements (package_summaries (Syntax.files p))).
Definition source_spec_package_rules_b (p : Syntax.Program) : bool := package_decls_unique_b p && main_pkgs_have_entry_b p.

Definition source_spec_valid_b (p : Syntax.Program) : bool := program_typedb p && source_spec_package_rules_b p.

(** The two factored package roots: at most one `main` per package, and at least one where required. *)
Definition PackageDeclsUnique (p : Syntax.Program) : Prop :=
  forall dir s, PackageMap.MapsTo dir s (package_summaries (Syntax.files p)) -> (summary_main_count s <= 1)%nat.
Definition MainPackagesHaveEntry (p : Syntax.Program) : Prop :=
  forall dir s, PackageMap.MapsTo dir s (package_summaries (Syntax.files p)) -> (1 <= summary_main_count s)%nat.
Definition PackageRulesValid (p : Syntax.Program) : Prop := PackageDeclsUnique p /\ MainPackagesHaveEntry p.

(** Each factored root reflects its own proposition directly. *)
Lemma package_decls_unique_b_iff : forall p, package_decls_unique_b p = true <-> PackageDeclsUnique p.
Proof.
  intro p. unfold package_decls_unique_b, PackageDeclsUnique.
  rewrite (Typing.forallb_iff_forall (fun b => Nat.leb (summary_main_count (snd b)) 1%nat) (fun b => (summary_main_count (snd b) <= 1)%nat)
             (PackageMap.elements (package_summaries (Syntax.files p))) (fun b => Nat.leb_le (summary_main_count (snd b)) 1%nat)).
  split.
  - intros Hf dir s Hmt.
    apply PackageFacts.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros Hall. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PackageFacts.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma main_pkgs_have_entry_b_iff : forall p, main_pkgs_have_entry_b p = true <-> MainPackagesHaveEntry p.
Proof.
  intro p. unfold main_pkgs_have_entry_b, MainPackagesHaveEntry.
  rewrite (Typing.forallb_iff_forall (fun b => Nat.leb 1%nat (summary_main_count (snd b))) (fun b => (1 <= summary_main_count (snd b))%nat)
             (PackageMap.elements (package_summaries (Syntax.files p))) (fun b => Nat.leb_le 1%nat (summary_main_count (snd b)))).
  split.
  - intros Hf dir s Hmt.
    apply PackageFacts.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros Hall. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PackageFacts.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

(** The specification decision reflects the factored rules directly, with no combined intermediary. *)
Lemma source_spec_package_rules_b_package_rules_valid : forall p, source_spec_package_rules_b p = true <-> PackageRulesValid p.
Proof.
  intro p. unfold source_spec_package_rules_b, PackageRulesValid.
  rewrite Bool.andb_true_iff, package_decls_unique_b_iff, main_pkgs_have_entry_b_iff. reflexivity.
Qed.

(** Package-summary exactness: the single fold is characterized, so grouping is one-pass and order-independent. *)
Fixpoint list_dir_count (dir : string) (l : list (FilePath.T * Syntax.File)) : nat :=
  match l with
  | [] => 0
  | b :: rest =>
      (if String.eqb (FilePath.parent (fst b)) dir then file_main_count (Syntax.declarations (snd b)) else 0)
      + list_dir_count dir rest
  end.
Definition list_dir_mem (dir : string) (l : list (FilePath.T * Syntax.File)) : bool :=
  existsb (fun b => String.eqb (FilePath.parent (fst b)) dir) l.

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
  - destruct (String.eqb (FilePath.parent (fst y)) dir), (String.eqb (FilePath.parent (fst x)) dir); reflexivity.
  - rewrite IHPermutation1; exact IHPermutation2.
Qed.
Lemma list_dir_count_perm : forall dir l1 l2, Permutation l1 l2 -> list_dir_count dir l1 = list_dir_count dir l2.
Proof.
  intros dir l1 l2 H; induction H; simpl; lia.
Qed.

(* the left fold matching [FileMap.fold] over the element list. *)
Definition package_foldl (l : list (FilePath.T * Syntax.File)) (acc : PackageMap.t PackageSummary) : PackageMap.t PackageSummary :=
  fold_left (fun a p => package_step (fst p) (snd p) a) l acc.
Lemma package_foldl_cons : forall k e rest acc,
  package_foldl ((k, e) :: rest) acc = package_foldl rest (package_step k e acc).
Proof. reflexivity. Qed.
Lemma package_summaries_foldl : forall fm,
  package_summaries fm = package_foldl (Syntax.file_bindings fm) (PackageMap.empty PackageSummary).
Proof. intro fm. unfold package_summaries, package_foldl. rewrite Syntax.FileMap.fold_1. reflexivity. Qed.

(* the fold CHARACTERIZATION: [find dir] is present iff a file belongs to [dir], and equals the exact sum. *)
Lemma package_foldl_find : forall l acc dir,
  PackageMap.find dir (package_foldl l acc)
  = (if list_dir_mem dir l
     then Some (MakePackageSummary (list_dir_count dir l + summary_count (PackageMap.find dir acc)))
     else PackageMap.find dir acc).
Proof.
  induction l as [|[k e] rest IH]; intros acc dir; [ reflexivity | ].
  rewrite package_foldl_cons, (IH (package_step k e acc) dir).
  unfold list_dir_mem; simpl existsb; simpl list_dir_count; cbn [fst snd].
  destruct (String.eqb (FilePath.parent k) dir) eqn:Edir; cbn [orb].
  - apply String.eqb_eq in Edir.
    unfold package_step, package_map_add_main. rewrite !PackageFacts.add_eq_o by exact Edir.
    cbn [summary_count summary_main_count]. rewrite !Edir.
    destruct (existsb (fun b => String.eqb (FilePath.parent (fst b)) dir) rest) eqn:Erest;
      [ | rewrite (list_dir_count_0 dir rest Erest) ]; f_equal; f_equal; lia.
  - apply String.eqb_neq in Edir.
    unfold package_step, package_map_add_main. rewrite !PackageFacts.add_neq_o by exact Edir. reflexivity.
Qed.

Definition package_main_count (dir : string) (fm : Syntax.Files) : nat := list_dir_count dir (Syntax.file_bindings fm).

Lemma package_summaries_find : forall fm dir,
  PackageMap.find dir (package_summaries fm)
  = (if list_dir_mem dir (Syntax.file_bindings fm)
     then Some (MakePackageSummary (package_main_count dir fm)) else None).
Proof.
  intros fm dir. rewrite package_summaries_foldl, package_foldl_find. unfold package_main_count.
  rewrite PackageFacts.empty_o. cbn [summary_count].
  destruct (list_dir_mem dir (Syntax.file_bindings fm)); [ f_equal; f_equal; lia | reflexivity ].
Qed.

(* THEOREM: every represented file contributes to its OWN parent-directory package (which is present). *)
Theorem file_in_package : forall fm path sf,
  Syntax.maps_to_file path sf fm -> PackageMap.In (FilePath.parent path) (package_summaries fm).
Proof.
  intros fm path sf Hmt.
  assert (Hin : In (path, sf) (Syntax.file_bindings fm)).
  { unfold Syntax.file_bindings. apply Syntax.FileFacts.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
    destruct Hmt as [[k' e'] [[Hk He] Hin']]. cbn in Hk, He. subst. exact Hin'. }
  exists (MakePackageSummary (package_main_count (FilePath.parent path) fm)).
  apply PackageFacts.find_mapsto_iff. rewrite package_summaries_find.
  assert (Hmem : list_dir_mem (FilePath.parent path) (Syntax.file_bindings fm) = true).
  { unfold list_dir_mem. apply existsb_exists. exists (path, sf).
    split; [ exact Hin | cbn [fst]; apply String.eqb_refl ]. }
  rewrite Hmem. reflexivity.
Qed.

(* THEOREM: no package summary exists without a file — a present [dir] is witnessed by a real file. *)
Theorem package_no_empty : forall fm dir,
  PackageMap.In dir (package_summaries fm) ->
  exists b, In b (Syntax.file_bindings fm) /\ FilePath.parent (fst b) = dir.
Proof.
  intros fm dir [s Hmt]. apply PackageFacts.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (Syntax.file_bindings fm)) eqn:Emem; [ | discriminate ].
  unfold list_dir_mem in Emem. apply existsb_exists in Emem. destruct Emem as [b [Hin Heq]].
  apply String.eqb_eq in Heq. exists b. split; [ exact Hin | exact Heq ].
Qed.

(* THEOREM: a package summary's main count IS the sum of [file_main_count] over its files. *)
Theorem package_summary_main_count : forall fm dir s,
  PackageMap.MapsTo dir s (package_summaries fm) -> summary_main_count s = package_main_count dir fm.
Proof.
  intros fm dir s Hmt. apply PackageFacts.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (Syntax.file_bindings fm)); [ | discriminate ].
  injection Hmt as <-. reflexivity.
Qed.

(* THEOREM: the empty file map yields the empty package map. *)
Theorem package_summaries_empty : forall dir,
  PackageMap.find dir (package_summaries empty_files) = None.
Proof.
  intro dir. rewrite package_summaries_find.
  replace (Syntax.file_bindings empty_files) with (@nil (FilePath.T * Syntax.File)); [ reflexivity | ].
  unfold Syntax.file_bindings, empty_files. symmetry. apply Collections.FileProperties.elements_empty.
Qed.

(* map-equal file collections yield map-equal package summaries, so the backing tree never leaks *)
Instance package_map_equal_equivalence : Equivalence (@PackageMap.Equal PackageSummary).
Proof.
  constructor.
  - intros m k; reflexivity.
  - intros m1 m2 H k; symmetry; apply H.
  - intros m1 m2 m3 H1 H2 k; transitivity (PackageMap.find k m2); [ apply H1 | apply H2 ].
Qed.
Lemma package_step_proper : Proper (Syntax.FileMap.E.eq ==> eq ==> PackageMap.Equal ==> PackageMap.Equal) package_step.
Proof.
  intros k1 k2 Hk e1 e2 He a1 a2 Ha dk.
  assert (Hkk : k1 = k2) by exact Hk. subst k2. subst e2.
  unfold package_step, package_map_add_main.
  destruct (String.eqb (FilePath.parent k1) dk) eqn:E.
  - apply String.eqb_eq in E. rewrite !PackageFacts.add_eq_o by exact E. rewrite (Ha (FilePath.parent k1)); reflexivity.
  - apply String.eqb_neq in E. rewrite !PackageFacts.add_neq_o by exact E. apply Ha.
Qed.
Lemma package_foldl_permutation : forall l1 l2 acc,
  Permutation l1 l2 -> PackageMap.Equal (package_foldl l1 acc) (package_foldl l2 acc).
Proof.
  intros l1 l2 acc Hperm dir. rewrite !package_foldl_find.
  rewrite (list_dir_mem_perm dir l1 l2 Hperm), (list_dir_count_perm dir l1 l2 Hperm). reflexivity.
Qed.
Lemma package_step_transpose : Collections.FileProperties.transpose_neqkey PackageMap.Equal package_step.
Proof.
  intros k1 k2 e1 e2 a _.
  change (package_step k1 e1 (package_step k2 e2 a)) with (package_foldl ((k2, e2) :: (k1, e1) :: nil) a).
  change (package_step k2 e2 (package_step k1 e1 a)) with (package_foldl ((k1, e1) :: (k2, e2) :: nil) a).
  apply package_foldl_permutation. apply perm_swap.
Qed.
Theorem package_summaries_equal : forall fm1 fm2,
  Syntax.FilesEqual fm1 fm2 -> PackageMap.Equal (package_summaries fm1) (package_summaries fm2).
Proof.
  intros fm1 fm2 Heq. unfold package_summaries.
  apply (Collections.FileProperties.fold_Equal package_map_equal_equivalence package_step_proper package_step_transpose). exact Heq.
Qed.

(* a permuted node list builds an equal map, so its package aggregation is unchanged *)
Theorem package_summaries_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  PackageMap.Equal (package_summaries (Syntax.files p1)) (package_summaries (Syntax.files p2)).
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply package_summaries_equal.
  unfold build_program in *.
  destruct (Syntax.files_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (Syntax.files_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [Syntax.files].
  exact (Syntax.files_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(* a package spans files, so its diagnostics anchor at a proof-backed key rather than a fake source node *)

Definition package_present_b (p : Syntax.Program) (key : string) : bool :=
  list_dir_mem key (Syntax.file_bindings (Syntax.files p)).

Record PackageRef (p : Syntax.Program) : Type := MakePackageRef {
  package_ref_key : string ;
  package_ref_ok  : package_present_b p package_ref_key = true
}.
Arguments package_ref_key {p} _.
Arguments package_ref_ok {p} _.

(** represented-package witness: a PackageRef's key names a real file in [p]. *)
Lemma package_ref_present : forall p (r : PackageRef p),
  exists path sf, Syntax.maps_to_file path sf (Syntax.files p) /\ FilePath.parent path = package_ref_key r.
Proof.
  intros p [k ok]; cbn. unfold package_present_b, list_dir_mem in ok.
  apply existsb_exists in ok. destruct ok as [b [Hin Heqb]]. apply String.eqb_eq in Heqb.
  exists (fst b), (snd b). split; [ | exact Heqb ].
  unfold Syntax.maps_to_file. apply Syntax.FileFacts.find_mapsto_iff.
  exact (Syntax.file_bindings_find (Syntax.files p) b Hin).
Qed.

(** identity IS key identity (the boolean proof field is irrelevant by UIP over bool — no axiom). *)
Lemma package_ref_key_inj : forall p (r1 r2 : PackageRef p),
  package_ref_key r1 = package_ref_key r2 -> r1 = r2.
Proof.
  intros p [k1 ok1] [k2 ok2] Heq; cbn in Heq; subst k2.
  f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(** construction from a real file binding: its package (parent directory) is present (the binding witnesses it). *)
Definition package_ref_of_binding (p : Syntax.Program) (b : FilePath.T * Syntax.File)
  (Hin : In b (Syntax.file_bindings (Syntax.files p))) : PackageRef p.
Proof.
  refine (MakePackageRef p (FilePath.parent (fst b)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists b. split; [ exact Hin | apply String.eqb_refl ].
Defined.

Lemma package_ref_of_binding_key : forall p b Hin,
  package_ref_key (package_ref_of_binding p b Hin) = FilePath.parent (fst b).
Proof. reflexivity. Qed.

(** construction from a validated file reference: the ref's own path witnesses its package. *)
Definition package_ref_of_fileref {p} (fr : Index.Snapshot.FileRef p) : PackageRef p.
Proof.
  refine (MakePackageRef p (FilePath.parent (Index.Snapshot.file_ref_path fr)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists (Index.Snapshot.file_ref_path fr, Index.Snapshot.file_ref_source fr). split.
  - apply Syntax.find_file_bindings.
    apply (Index.Snapshot.file_of_path_source_exact p (Index.Snapshot.file_ref_path fr) fr).
    apply Index.Snapshot.file_of_path_complete.
  - apply String.eqb_refl.
Defined.

Lemma package_ref_of_fileref_key : forall p (fr : Index.Snapshot.FileRef p),
  package_ref_key (package_ref_of_fileref fr) = FilePath.parent (Index.Snapshot.file_ref_path fr).
Proof. reflexivity. Qed.

(* the diagnostic core: exact-snapshot anchors and structured values, so a wrong combination cannot be built *)

Inductive DiagnosticAnchor (p : Syntax.Program) : Type :=
| AtNode    : Index.Snapshot.NodeRef p -> DiagnosticAnchor p
| AtFile    : Index.Snapshot.FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.
Arguments AtNode {p} _.  Arguments AtFile {p} _.  Arguments AtPackage {p} _.  Arguments AtProgram {p}.

(* the four diagnostic reasons; a nested conversion reports its innermost failure first *)
Inductive DiagnosticReason (p : Syntax.Program) : Type :=
| InvalidConversion
    (primary : Index.ExprRef p) (target_ref : Index.TypeNameRef p) (operand_ref : Index.ExprRef p)
    (outer_context : list (Index.ExprRef p))
    (target : Typing.SemanticType) (operand_status : Typing.ConstantInfo)
| DefaultNotRepresentable
    (primary : Index.ExprRef p) (exact_constant : Typing.Constant) (default_target : Typing.SemanticType)
| MainRedeclared
    (later_primary : Index.DeclRef p) (earlier_related : Index.DeclRef p)
| MissingMainEntry
    (package_primary : PackageRef p)
(* the build-output planning failure: a sole main package whose default output name is an existing directory *)
| BuildOutputIsDirectory
    (package_primary : PackageRef p) (output_name : string).
Arguments InvalidConversion {p} _ _ _ _ _ _.  Arguments DefaultNotRepresentable {p} _ _ _.
Arguments MainRedeclared {p} _ _.  Arguments MissingMainEntry {p} _.  Arguments BuildOutputIsDirectory {p} _ _.

Inductive DiagnosticCode : Type :=
| CodeInvalidConversion | CodeDefaultNotRepresentable | CodeMainRedeclared | CodeMissingMainEntry | CodeBuildOutputIsDirectory.

Definition diagnostic_code {p} (d : DiagnosticReason p) : DiagnosticCode :=
  match d with
  | InvalidConversion _ _ _ _ _ _ => CodeInvalidConversion
  | DefaultNotRepresentable _ _ _ => CodeDefaultNotRepresentable
  | MainRedeclared _ _           => CodeMainRedeclared
  | MissingMainEntry _               => CodeMissingMainEntry
  | BuildOutputIsDirectory _ _  => CodeBuildOutputIsDirectory
  end.

Definition diagnostic_primary {p} (d : DiagnosticReason p) : DiagnosticAnchor p :=
  match d with
  | InvalidConversion pr _ _ _ _ _  => AtNode (Index.erase_ref pr)
  | DefaultNotRepresentable pr _ _  => AtNode (Index.erase_ref pr)
  | MainRedeclared later _           => AtNode (Index.erase_ref later)
  | MissingMainEntry pk                  => AtPackage pk
  | BuildOutputIsDirectory pk _     => AtPackage pk
  end.

Definition diagnostic_related {p} (d : DiagnosticReason p) : list (DiagnosticAnchor p) :=
  match d with
  | InvalidConversion _ _ _ outer _ _ => map (fun r => AtNode (Index.erase_ref r)) outer
  | DefaultNotRepresentable _ _ _   => []
  | MainRedeclared _ earlier         => [AtNode (Index.erase_ref earlier)]
  | MissingMainEntry _                   => []
  | BuildOutputIsDirectory _ _      => []
  end.

(** the primary anchor is always an exact-snapshot handle whose CODE matches the reason. *)
Lemma diagnostic_code_primary_consistent : forall p (d : DiagnosticReason p),
  match diagnostic_code d, diagnostic_primary d with
  | CodeMissingMainEntry, AtPackage _ | CodeBuildOutputIsDirectory, AtPackage _ => True
  | CodeInvalidConversion, AtNode _ | CodeDefaultNotRepresentable, AtNode _ | CodeMainRedeclared, AtNode _ => True
  | _, _ => False
  end.
Proof. intros p [pr tr o t s|pr c dt|l e|pk|pk nm]; cbn; exact I. Qed.

(* erasure projects a snapshot-indexed reason to a snapshot-independent one, so two reports can be compared *)

Inductive ErasedAnchor : Type :=
| AnchorNode    : Index.Key -> ErasedAnchor
| AnchorFile    : FilePath.T -> ErasedAnchor
| AnchorPackage : string -> ErasedAnchor
| AnchorProgram : ErasedAnchor.

Definition erase_anchor {p} (a : DiagnosticAnchor p) : ErasedAnchor :=
  match a with
  | AtNode r     => AnchorNode (Index.Snapshot.node_ref_key r)
  | AtFile fr    => AnchorFile (Index.Snapshot.file_ref_path fr)
  | AtPackage pk => AnchorPackage (package_ref_key pk)
  | AtProgram    => AnchorProgram
  end.

Record ErasedDiagnostic : Type := MakeErased {
  erased_code    : DiagnosticCode ;
  erased_primary : ErasedAnchor ;
  erased_related : list ErasedAnchor ;
  diagnostic_target  : option Typing.SemanticType ;
  (* the erased build-output payload, so two collisions with different names compare unequal *)
  diagnostic_output  : option string ;
  (* the erased source target comes through the retained reference, so `byte` and `uint8` compare unequal *)
  diagnostic_source_target : option Syntax.TypeExpr
}.

(* the erased target type, where the reason carries one *)
Definition erased_target {p} (d : DiagnosticReason p) : option Typing.SemanticType :=
  match d with
  | InvalidConversion _ _ _ _ t _  => Some t
  | DefaultNotRepresentable _ _ dt => Some dt
  | MainRedeclared _ _              => None
  | MissingMainEntry _                  => None
  | BuildOutputIsDirectory _ _     => None
  end.

(* only the build-output reason carries a planned output name *)
Definition erased_output {p} (d : DiagnosticReason p) : option string :=
  match d with
  | InvalidConversion _ _ _ _ _ _  => None
  | DefaultNotRepresentable _ _ _  => None
  | MainRedeclared _ _              => None
  | MissingMainEntry _                  => None
  | BuildOutputIsDirectory _ nm    => Some nm
  end.

(* the erased source target, recovered through the reference rather than reverse-mapped from the resolved type *)
Definition erased_source_target {p} (d : DiagnosticReason p) : option Syntax.TypeExpr :=
  match d with
  | InvalidConversion _ tr _ _ _ _ => Index.type_name_ref_syntax tr
  | _ => None
  end.

Definition erase_diagnostic {p} (d : DiagnosticReason p) : ErasedDiagnostic :=
  MakeErased (diagnostic_code d) (erase_anchor (diagnostic_primary d))
    (map erase_anchor (diagnostic_related d)) (erased_target d) (erased_output d) (erased_source_target d).

(* erasing keeps the code, the primary key identity, and the related anchors in canonical order *)
Lemma erase_diagnostic_code {p} (d : DiagnosticReason p) : erased_code (erase_diagnostic d) = diagnostic_code d.
Proof. reflexivity. Qed.

Lemma erase_diagnostic_primary {p} (d : DiagnosticReason p) :
  erased_primary (erase_diagnostic d) = erase_anchor (diagnostic_primary d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related {p} (d : DiagnosticReason p) :
  erased_related (erase_diagnostic d) = map erase_anchor (diagnostic_related d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related_length {p} (d : DiagnosticReason p) :
  length (erased_related (erase_diagnostic d)) = length (diagnostic_related d).
Proof.
  cbn [erased_related erase_diagnostic].
  induction (diagnostic_related d) as [|x xs IH]; cbn [map length]; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma erase_diagnostic_output {p} (d : DiagnosticReason p) :
  diagnostic_output (erase_diagnostic d) = erased_output d.
Proof. reflexivity. Qed.

(* the erased report keeps the collision name only where the reason has one *)
Lemma erased_output_iff_build_output {p} (d : DiagnosticReason p) :
  (exists nm, diagnostic_output (erase_diagnostic d) = Some nm) <-> diagnostic_code d = CodeBuildOutputIsDirectory.
Proof. destruct d; cbn; split; try (intros [nm H]; discriminate); try discriminate; eauto. Qed.

(* one fact per expression occurrence: its constant status, plus its resolution where the context is a use *)

Record ExpressionFact : Type := MakeExpressionFact {
  const_status : Typing.ConstantInfo ;
  use_resolved : option Typing.ResolvedConstant
}.

Definition resolved_type_at (f : ExpressionFact) : option Typing.SemanticType :=
  option_map Typing.resolved_constant_type (use_resolved f).
Definition resolved_constant_at (f : ExpressionFact) : option Typing.Constant :=
  option_map Typing.resolved_constant_exact (use_resolved f).

(** an occurrence resolves exactly when it is a println argument that resolves *)
Definition occurrence_use_resolved (o : Index.Occurrence) : option Typing.ResolvedConstant :=
  match Index.occurrence_role o with
  | Index.PrintlnArgument _ =>
      match Index.view_expr o with Some e => resolve_constant Typing.PrintlnArgument e | None => None end
  | _ => None
  end.

(** resolution reads the stored status and the role, and never rescans the raw expression *)
Definition use_resolved_of_input (role : Index.Role) (ci : Typing.ConstantInfo) : option Typing.ResolvedConstant :=
  match role with
  | Index.PrintlnArgument _ =>
      match Typing.resolve_constant_info ci with
      | Some rc => if use_allowsb Typing.PrintlnArgument (Typing.resolved_constant_type rc) then Some rc else None
      | None => None
      end
  | _ => None
  end.

Lemma use_resolved_of_input_eq : forall o e ci,
  Index.view_expr o = Some e -> constant_info e = Some ci ->
  use_resolved_of_input (Index.occurrence_role o) ci = occurrence_use_resolved o.
Proof.
  intros o e ci Hv Hc. unfold use_resolved_of_input, occurrence_use_resolved.
  destruct (Index.occurrence_role o) as [ | | ai | si | ain | | ]; try reflexivity.
  rewrite Hv. unfold resolve_constant. rewrite Hc. reflexivity.
Qed.

(** the fact of a single occurrence: [Some] exactly for an expression occurrence whose [constant_info] succeeds. *)
Definition occurrence_expr_fact (o : Index.Occurrence) : option ExpressionFact :=
  match Index.view_expr o with
  | Some e => match constant_info e with
              | Some ci => Some (MakeExpressionFact ci (occurrence_use_resolved o))
              | None => None
              end
  | None => None
  end.

(** an occurrence has a fact exactly when it is an expression whose constant analysis succeeds *)
Lemma occurrence_expr_fact_status : forall o e ci,
  Index.view_expr o = Some e -> constant_info e = Some ci ->
  occurrence_expr_fact o = Some (MakeExpressionFact ci (occurrence_use_resolved o)).
Proof. intros o e ci Hv Hc. unfold occurrence_expr_fact. rewrite Hv, Hc. reflexivity. Qed.

Lemma occurrence_expr_fact_none_nonexpr : forall o,
  Index.view_expr o = None -> occurrence_expr_fact o = None.
Proof. intros o Hv. unfold occurrence_expr_fact. rewrite Hv. reflexivity. Qed.

(** the production outcome authority: bottom-up, reading each retained reference rather than rescanning *)
Inductive ExpressionOutcome (p : Syntax.Program) : Type :=
  | ExpressionSuccess       : ExpressionFact -> ExpressionOutcome p                 (* a leaf or a successful conversion *)
  | ConversionFailure : Index.ExprRef p -> Index.TypeNameRef p -> Index.ExprRef p -> Typing.SemanticType -> Typing.ConstantInfo -> ExpressionOutcome p
      (* a local invalid conversion carries its own references, resolved target and operand status *)
  | ChildFailure : ExpressionOutcome p.                           (* blocked: the operand's outcome was a real non-success *)
Arguments ExpressionSuccess {p} _.  Arguments ConversionFailure {p} _ _ _ _ _.  Arguments ChildFailure {p}.

(** the per-file fact map folds the visit stream; distinct keys mean the fold never overwrites *)
Definition add_occ_fact {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
    (m : Index.KeyMap.t ExpressionFact) : Index.KeyMap.t ExpressionFact :=
  match occurrence_expr_fact (snd ro) with
  | Some f => Index.KeyMap.add (Index.Snapshot.node_ref_key (fst ro)) f m
  | None => m
  end.

Lemma no_duplicates_map_inj {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj H. induction H as [|x l Hx Hnd IH]; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]]. apply Hinj in Hfy. subst y. contradiction.
  - exact IH.
Qed.

(** the [visit_file] refs have DISTINCT NodeKeys (same file, distinct local ids). *)
Lemma visit_file_key_nodup {p} (fr : Index.Snapshot.FileRef p) :
  NoDup (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (Index.Snapshot.visit_file fr)).
Proof.
  assert (Hmap : map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (Index.Snapshot.visit_file fr)
    = map (fun ro => Index.MakeKey (Index.Snapshot.file_ref_path fr) (Index.Snapshot.node_ref_local (fst ro)))
          (Index.Snapshot.visit_file fr)).
  { apply map_ext_in. intros [r occ] Hin. cbn [fst]. rewrite Index.Snapshot.node_ref_key_eq.
    destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity. }
  rewrite Hmap, <- (map_map (fun ro => Index.Snapshot.node_ref_local (fst ro))
                            (Index.MakeKey (Index.Snapshot.file_ref_path fr))).
  apply no_duplicates_map_inj; [ intros x y H; injection H as H; exact H | apply Index.Snapshot.visit_file_nodup ].
Qed.

Lemma facts_not_in_domain {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) (k : Index.Key) :
  ~ In k (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) l) ->
  Index.KeyMap.find k (fold_right add_occ_fact (Index.KeyMap.empty ExpressionFact) l) = None.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hni; simpl.
  - apply Index.KeyFacts.empty_o.
  - simpl in Hni.
    assert (Hne : Index.Snapshot.node_ref_key r0 <> k) by (intro H; apply Hni; left; exact H).
    assert (Hrest : ~ In k (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) rest))
      by (intro H; apply Hni; right; exact H).
    unfold add_occ_fact; cbn [snd fst]. destruct (occurrence_expr_fact occ0) as [f|].
    + rewrite Index.key_map_add_unequal by exact Hne. exact (IH Hrest).
    + exact (IH Hrest).
Qed.

Lemma fold_facts_find {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) r occ :
  NoDup (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) l) ->
  In (r, occ) l ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r)
    (fold_right add_occ_fact (Index.KeyMap.empty ExpressionFact) l) = occurrence_expr_fact occ.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hnd Hin; [ destruct Hin |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  simpl. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. unfold add_occ_fact; cbn [snd fst].
    destruct (occurrence_expr_fact occ0) as [f|] eqn:Ef.
    + rewrite Index.key_map_add_equal. reflexivity.
    + apply facts_not_in_domain. exact Hni.
  - assert (Hin' : In (Index.Snapshot.node_ref_key r)
             (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) rest)).
    { apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hin]. }
    assert (Hkr : Index.Snapshot.node_ref_key r <> Index.Snapshot.node_ref_key r0)
      by (intro Hk; apply Hni; rewrite <- Hk; exact Hin').
    unfold add_occ_fact; cbn [snd fst]. destruct (occurrence_expr_fact occ0) as [f0|].
    + rewrite Index.key_map_add_unequal by (intro Hk; apply Hkr; symmetry; exact Hk).
      exact (IH Hnd' Hin).
    + exact (IH Hnd' Hin).
Qed.


(* ---- program-wide visit stream + fact map (lifted to the whole program) ---- *)

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
Definition binding_visit (p : Syntax.Program) (b : FilePath.T * Syntax.File)
  : list (Index.Snapshot.NodeRef p * Index.Occurrence) :=
  match Index.Snapshot.file_of_path p (fst b) with
  | Some fr => Index.Snapshot.visit_file fr
  | None => []
  end.

(** the retained per-file visit blocks, each file visited once in canonical path order *)
Definition program_blocks (p : Syntax.Program) : list (list (Index.Snapshot.NodeRef p * Index.Occurrence)) :=
  map (binding_visit p) (Syntax.file_bindings (Syntax.files p)).

(** the WHOLE-PROGRAM visit stream: the retained blocks flattened (each file visited once, path order). *)
Definition program_visit (p : Syntax.Program) : list (Index.Snapshot.NodeRef p * Index.Occurrence) :=
  concat (program_blocks p).

(** the flattened stream IS the per-binding flat_map (used by the existing membership/fold proofs). *)
Lemma program_visit_flat_map (p : Syntax.Program) :
  program_visit p = flat_map (binding_visit p) (Syntax.file_bindings (Syntax.files p)).
Proof. unfold program_visit, program_blocks. rewrite flat_map_concat_map. reflexivity. Qed.

(** every visited pair's occurrence is its own reference's source occurrence *)
Lemma program_visit_occ_is_source (p : Syntax.Program) (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (program_visit p) -> occ = Index.Snapshot.source_occurrence_of_ref r.
Proof.
  intro Hin. rewrite program_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [_ Hrb]].
  unfold binding_visit in Hrb. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|]; [|destruct Hrb].
  destruct (Index.Snapshot.visit_file_view p fr r occ Hrb) as [Ho _]. exact Ho.
Qed.

(** a visited EXPRESSION occurrence's reference refines: [as_expr] succeeds and erases back to [r]. *)
Lemma program_visit_as_expr (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p) occ e :
  In (r, occ) (program_visit p) -> Index.view_expr occ = Some e ->
  exists er, Index.as_expr idx r = Some er /\ Index.erase_ref er = r.
Proof.
  intros Hin Hv. rewrite (program_visit_occ_is_source p r occ Hin) in Hv.
  assert (Hk : Index.Snapshot.node_kind idx r = Index.ExpressionKind)
    by (rewrite (Index.Snapshot.node_kind_matches_source p idx r); exact (Index.view_expr_kind _ e Hv)).
  destruct (Index.as_kind_complete idx r Index.ExpressionKind Hk) as [er [Hae Her]].
  exists er. split; [ exact Hae | exact Her ].
Qed.

(** every key in one binding's block has that binding's path (used for cross-file disjointness). *)
Lemma binding_visit_key_file : forall p b k,
  In k (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (binding_visit p b)) ->
  Index.key_path k = fst b.
Proof.
  intros p b k Hin. unfold binding_visit in Hin.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [| destruct Hin].
  apply in_map_iff in Hin. destruct Hin as [[r occ] [Hk Hin]]. cbn [fst] in Hk. subst k.
  rewrite Index.Snapshot.node_ref_key_eq. cbn [Index.key_path].
  destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf.
  exact (Index.Snapshot.file_of_path_sound p (fst b) fr Ef).
Qed.

(** program-wide keys are DISTINCT: distinct locals within a file, distinct paths across files. *)
Lemma program_visit_key_nodup (p : Syntax.Program) :
  NoDup (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (program_visit p)).
Proof.
  rewrite program_visit_flat_map, map_flat_map.
  apply (nodup_flat_map_tag
           (fun b => map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (binding_visit p b))
           Index.key_path (fun b => fst b) (Syntax.file_bindings (Syntax.files p))).
  - intros b _. unfold binding_visit.
    destruct (Index.Snapshot.file_of_path p (fst b)); [ apply visit_file_key_nodup | constructor ].
  - intros b k _ Hin. exact (binding_visit_key_file p b k Hin).
  - apply Syntax.file_bindings_nodup_keys.
Qed.

(* the specification map is source-determined; the production map projects the one retained forest *)

Lemma occurrences_expr_head_ex : forall e parent role start,
  exists occ, In (start, occ) (Index.occurrences_expr parent role start e) /\ Index.view_expr occ = Some e.
Proof. intros e parent role start; destruct e; cbn [Index.occurrences_expr]; eexists; (split; [left; reflexivity|reflexivity]). Qed.

(* the head of a subtree stream carries exactly the role it was passed *)
Lemma occurrences_expr_head_role : forall e parent role start,
  exists occ, In (start, occ) (Index.occurrences_expr parent role start e)
    /\ Index.view_expr occ = Some e /\ Index.occurrence_role occ = role.
Proof.
  intros e parent role start; destruct e; cbn [Index.occurrences_expr]; eexists;
    (split; [left; reflexivity | split; [reflexivity | cbn [Index.occurrence_role]; reflexivity]]).
Qed.

Lemma occurrences_expr_operand : forall e parent role start me occ ce x,
  In (me, occ) (Index.occurrences_expr parent role start e) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_expr parent role start e)
    /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts y IHy ]; intros parent role start me occ ce x Hin Hv Hc.
  (* leaves: the only occurrence is the leaf, whose view has no Typing.expression_child *)
  1,2,3,4,5,6: cbn [Index.occurrences_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
               injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv;
               injection Hv as Hce; subst ce; cbn [Typing.expression_child] in Hc; discriminate Hc.
  (* a conversion, then its type-name child, then its operand subtree two past the conversion *)
  cbn [Index.occurrences_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as Hid Hocc; rewrite <- Hid; rewrite <- Hocc in Hv;
    cbn [Index.view_expr Index.occurrence_view] in Hv; injection Hv as Hce; subst ce;
    cbn [Typing.expression_child] in Hc; injection Hc as Hx; subst x.
    destruct (occurrences_expr_head_role y start Index.ConversionOperand (Pos.succ (Pos.succ start)))
      as [occ' [Hin' [Hv' Hr']]].
    exists occ'; split; [right; right; exact Hin' | split; [exact Hv' | exact Hr']].
  - destruct Hin as [Heq|Hin].
    + (* the type-name occurrence has no expression view *)
      injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv; discriminate Hv.
    + destruct (IHy start Index.ConversionOperand (Pos.succ (Pos.succ start)) me occ ce x Hin Hv Hc)
        as [occ' [Hin' [Hv' Hr']]].
      exists occ'; split; [right; right; exact Hin' | split; [exact Hv' | exact Hr']].
Qed.

Lemma in_app_operand {L1 L2 : list (positive * Index.Occurrence)} me occ x :
  (forall M O ce X, In (M, O) L1 -> Index.view_expr O = Some ce -> Typing.expression_child ce = Some X ->
     exists O', In (Pos.succ (Pos.succ M), O') L1 /\ Index.view_expr O' = Some X /\ Index.occurrence_role O' = Index.ConversionOperand) ->
  (forall M O ce X, In (M, O) L2 -> Index.view_expr O = Some ce -> Typing.expression_child ce = Some X ->
     exists O', In (Pos.succ (Pos.succ M), O') L2 /\ Index.view_expr O' = Some X /\ Index.occurrence_role O' = Index.ConversionOperand) ->
  forall ce, In (me, occ) (L1 ++ L2) -> Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (L1 ++ L2) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  intros H1 H2 ce Hin Hv Hc. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; left; exact Hin' | exact Hv'].
  - destruct (H2 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_args_operand : forall es parent aidx start me occ ce x,
  In (me, occ) (Index.occurrences_args parent aidx start es) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_args parent aidx start es) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ce x Hin Hv Hc; cbn [Index.occurrences_args] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. unfold Index.occurrences_arg. eapply occurrences_expr_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occurrences_stmt_operand : forall s parent sidx start me occ ce x,
  In (me, occ) (Index.occurrences_stmt parent sidx start s) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_stmt parent sidx start s) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  intros [args] parent sidx start me occ ce x Hin Hv Hc. cbn [Index.occurrences_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_args_operand args start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_stmts_operand : forall ss parent sidx start me occ ce x,
  In (me, occ) (Index.occurrences_stmts parent sidx start ss) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_stmts parent sidx start ss) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ce x Hin Hv Hc; cbn [Index.occurrences_stmts] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occurrences_stmt_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occurrences_decl_operand : forall d parent didx start me occ ce x,
  In (me, occ) (Index.occurrences_decl parent didx start d) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_decl parent didx start d) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  intros [body] parent didx start me occ ce x Hin Hv Hc. cbn [Index.occurrences_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_stmts_operand body start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_decls_operand : forall ds parent didx start me occ ce x,
  In (me, occ) (Index.occurrences_decls parent didx start ds) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_decls parent didx start ds) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ce x Hin Hv Hc; cbn [Index.occurrences_decls] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occurrences_decl_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occurrences_file_operand : forall f me occ ce x,
  In (me, occ) (Index.occurrences_file f) ->
  Index.view_expr occ = Some ce -> Typing.expression_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (Index.occurrences_file f) /\ Index.view_expr occ' = Some x /\ Index.occurrence_role occ' = Index.ConversionOperand.
Proof.
  intros f me occ ce x Hin Hv Hc. unfold Index.occurrences_file in *.
  destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_decls_operand (Syntax.declarations f) Index.root_id 0 (Pos.succ Index.package_id) me occ ce x Hin Hv Hc)
      as [occ' [Hin' Hv']].
    exists occ'. split; [right; right; exact Hin' | exact Hv'].
Qed.

(* a conversion's source type-name occurrence sits at the next local id, one child before the operand *)
Definition expression_conv_target (e : Syntax.Expr) : option Syntax.TypeExpr :=
  match e with Syntax.Convert ts _ => Some ts | _ => None end.

Lemma expression_conv_target_some : forall e ts, expression_conv_target e = Some ts -> exists x, e = Syntax.Convert ts x.
Proof.
  intros e ts H. destruct e as [ | | | | | | ts0 x]; cbn in H; try discriminate H.
  injection H as H0. subst ts0. exists x. reflexivity.
Qed.

Lemma occurrences_expr_type_name : forall e parent role start me occ ts x,
  In (me, occ) (Index.occurrences_expr parent role start e) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_expr parent role start e) /\ Index.view_typename occ' = Some ts.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ty y IHy ]; intros parent role start me occ ts x Hin Hv.
  1,2,3,4,5,6: cbn [Index.occurrences_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
    injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv; discriminate Hv.
  cbn [Index.occurrences_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv; injection Hv as <- <-.
    eexists. split; [ right; left; reflexivity | cbn [Index.view_typename Index.occurrence_view]; reflexivity ].
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv; discriminate Hv.
    + destruct (IHy start Index.ConversionOperand (Pos.succ (Pos.succ start)) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
      exists occ'; split; [ right; right; exact Hin' | exact Hv' ].
Qed.

Lemma in_app_type_name {L1 L2 : list (positive * Index.Occurrence)} me occ ts x :
  (forall M O T X, In (M, O) L1 -> Index.view_expr O = Some (Syntax.Convert T X) ->
     exists O', In (Pos.succ M, O') L1 /\ Index.view_typename O' = Some T) ->
  (forall M O T X, In (M, O) L2 -> Index.view_expr O = Some (Syntax.Convert T X) ->
     exists O', In (Pos.succ M, O') L2 /\ Index.view_typename O' = Some T) ->
  In (me, occ) (L1 ++ L2) -> Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (L1 ++ L2) /\ Index.view_typename occ' = Some ts.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 me occ ts x Hin Hv) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; left; exact Hin' | exact Hv'].
  - destruct (H2 me occ ts x Hin Hv) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_args_type_name : forall es parent aidx start me occ ts x,
  In (me, occ) (Index.occurrences_args parent aidx start es) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_args parent aidx start es) /\ Index.view_typename occ' = Some ts.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ts x Hin Hv; cbn [Index.occurrences_args] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. unfold Index.occurrences_arg. eapply occurrences_expr_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_stmt_type_name : forall s parent sidx start me occ ts x,
  In (me, occ) (Index.occurrences_stmt parent sidx start s) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_stmt parent sidx start s) /\ Index.view_typename occ' = Some ts.
Proof.
  intros [args] parent sidx start me occ ts x Hin Hv. cbn [Index.occurrences_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_args_type_name args start 0 (Pos.succ start) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_stmts_type_name : forall ss parent sidx start me occ ts x,
  In (me, occ) (Index.occurrences_stmts parent sidx start ss) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_stmts parent sidx start ss) /\ Index.view_typename occ' = Some ts.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ts x Hin Hv; cbn [Index.occurrences_stmts] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. eapply occurrences_stmt_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_decl_type_name : forall d parent didx start me occ ts x,
  In (me, occ) (Index.occurrences_decl parent didx start d) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_decl parent didx start d) /\ Index.view_typename occ' = Some ts.
Proof.
  intros [body] parent didx start me occ ts x Hin Hv. cbn [Index.occurrences_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_stmts_type_name body start 0 (Pos.succ start) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occurrences_decls_type_name : forall ds parent didx start me occ ts x,
  In (me, occ) (Index.occurrences_decls parent didx start ds) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_decls parent didx start ds) /\ Index.view_typename occ' = Some ts.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ts x Hin Hv; cbn [Index.occurrences_decls] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. eapply occurrences_decl_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_file_type_name : forall f me occ ts x,
  In (me, occ) (Index.occurrences_file f) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists occ', In (Pos.succ me, occ') (Index.occurrences_file f) /\ Index.view_typename occ' = Some ts.
Proof.
  intros f me occ ts x Hin Hv. unfold Index.occurrences_file in *.
  destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - destruct (occurrences_decls_type_name (Syntax.declarations f) Index.root_id 0 (Pos.succ Index.package_id) me occ ts x Hin Hv)
      as [occ' [Hin' Hv']].
    exists occ'. split; [right; right; exact Hin' | exact Hv'].
Qed.

(* only a conversion's type-name child carries a type-name view, so the view identifies the target role *)

Lemma occurrences_expr_typename_role : forall e parent role start me occ ts,
  In (me, occ) (Index.occurrences_expr parent role start e) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ty y IHy ]; intros parent role start me occ ts Hin Hv.
  1,2,3,4,5,6: cbn [Index.occurrences_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
    injection Heq as <- <-; cbn [Index.view_typename Index.occurrence_view] in Hv; discriminate Hv.
  cbn [Index.occurrences_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [Index.view_typename Index.occurrence_view] in Hv; discriminate Hv.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [Index.occurrence_role]; reflexivity.
    + exact (IHy start Index.ConversionOperand (Pos.succ (Pos.succ start)) me occ ts Hin Hv).
Qed.

Lemma in_app_typename_role {L1 L2 : list (positive * Index.Occurrence)} me occ ts :
  (forall M O T, In (M, O) L1 -> Index.view_typename O = Some T -> Index.occurrence_role O = Index.ConversionTarget) ->
  (forall M O T, In (M, O) L2 -> Index.view_typename O = Some T -> Index.occurrence_role O = Index.ConversionTarget) ->
  In (me, occ) (L1 ++ L2) -> Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    [ exact (H1 me occ ts Hin Hv) | exact (H2 me occ ts Hin Hv) ].
Qed.

Lemma occurrences_args_typename_role : forall es parent aidx start me occ ts,
  In (me, occ) (Index.occurrences_args parent aidx start es) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ts Hin Hv; cbn [Index.occurrences_args] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. unfold Index.occurrences_arg. eapply occurrences_expr_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_stmt_typename_role : forall s parent sidx start me occ ts,
  In (me, occ) (Index.occurrences_stmt parent sidx start s) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  intros [args] parent sidx start me occ ts Hin Hv. cbn [Index.occurrences_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_typename Index.occurrence_view] in Hv. discriminate Hv.
  - exact (occurrences_args_typename_role args start 0 (Pos.succ start) me occ ts Hin Hv).
Qed.

Lemma occurrences_stmts_typename_role : forall ss parent sidx start me occ ts,
  In (me, occ) (Index.occurrences_stmts parent sidx start ss) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ts Hin Hv; cbn [Index.occurrences_stmts] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. eapply occurrences_stmt_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_decl_typename_role : forall d parent didx start me occ ts,
  In (me, occ) (Index.occurrences_decl parent didx start d) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  intros [body] parent didx start me occ ts Hin Hv. cbn [Index.occurrences_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_typename Index.occurrence_view] in Hv. discriminate Hv.
  - exact (occurrences_stmts_typename_role body start 0 (Pos.succ start) me occ ts Hin Hv).
Qed.

Lemma occurrences_decls_typename_role : forall ds parent didx start me occ ts,
  In (me, occ) (Index.occurrences_decls parent didx start ds) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ts Hin Hv; cbn [Index.occurrences_decls] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. eapply occurrences_decl_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occurrences_file_typename_role : forall f me occ ts,
  In (me, occ) (Index.occurrences_file f) ->
  Index.view_typename occ = Some ts -> Index.occurrence_role occ = Index.ConversionTarget.
Proof.
  intros f me occ ts Hin Hv. unfold Index.occurrences_file in *.
  destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [Index.view_typename Index.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [Index.view_typename Index.occurrence_view] in Hv. discriminate Hv.
  - exact (occurrences_decls_typename_role (Syntax.declarations f) Index.root_id 0 (Pos.succ Index.package_id) me occ ts Hin Hv).
Qed.

(* on a typed program every visited expression occurrence has a successful constant analysis *)
Lemma expression_typedb_const_info : forall u e, expression_typedb u e = true -> exists ci, constant_info e = Some ci.
Proof.
  intros u e H. unfold expression_typedb in H.
  destruct (resolve u e) as [t|] eqn:Hr; [|discriminate H].
  unfold resolve in Hr.
  destruct (resolve_constant u e) as [rc|] eqn:Hrc; cbn [option_map] in Hr; [|discriminate Hr].
  destruct (Typing.resolve_constant_sound predeclared_type u e rc Hrc) as [ci [Hci _]]. exists ci; exact Hci.
Qed.

(* one downward step: a node whose [constant_info] succeeds has an expression child whose [constant_info] succeeds. *)
Lemma const_info_child_some : forall e x ci,
  Typing.expression_child e = Some x -> constant_info e = Some ci -> exists cix, constant_info x = Some cix.
Proof.
  intros e x ci Hc Hci. rewrite Typing.constant_info_step_reflect, Hc in Hci.
  destruct e as [ b|n1|n2|s| df | dcx | ts y ]; cbn [Typing.expression_child] in Hc; try discriminate Hc;
    cbn [Typing.constant_info_step] in Hci;
    (destruct (constant_info x) as [cix|]; [ exists cix; reflexivity | discriminate Hci ]).
Qed.

(* success at the root propagates to every occurrence of the subtree stream *)
Lemma occurrences_expr_const_info_some : forall e parent role pos me occ e' ci,
  constant_info e = Some ci ->
  In (me, occ) (Index.occurrences_expr parent role pos e) ->
  Index.view_expr occ = Some e' -> exists ci', constant_info e' = Some ci'.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts y IHy ];
    intros parent role pos me occ e' ci Hci Hin Hv.
  1,2,3,4,5,6: cbn [Index.occurrences_expr] in Hin; destruct Hin as [Heq|[]];
    injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv;
    injection Hv as <-; exists ci; exact Hci.
  (* conversion: conv head (view = the conversion), type-name (view = None, discriminated), operand subtree (IH) *)
  cbn [Index.occurrences_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv;
    injection Hv as <-; exists ci; exact Hci.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [Index.view_expr Index.occurrence_view] in Hv; discriminate Hv.
    + assert (Hy : exists ciy, constant_info y = Some ciy)
        by (cbn [Typing.constant_info] in Hci; destruct (constant_info y) as [ciy|];
            [ eexists; reflexivity | discriminate Hci ]);
      destruct Hy as [ciy Hciy];
      exact (IHy pos Index.ConversionOperand (Pos.succ (Pos.succ pos)) me occ e' ciy Hciy Hin Hv).
Qed.

Lemma in_app_const_info_some {L1 L2 : list (positive * Index.Occurrence)} me occ e' :
  (forall M O E, In (M, O) L1 -> Index.view_expr O = Some E -> exists ci, constant_info E = Some ci) ->
  (forall M O E, In (M, O) L2 -> Index.view_expr O = Some E -> exists ci, constant_info E = Some ci) ->
  In (me, occ) (L1 ++ L2) -> Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    [ exact (H1 me occ e' Hin Hv) | exact (H2 me occ e' Hin Hv) ].
Qed.

Lemma occurrences_arg_const_info_some : forall e parent aidx pos me occ e',
  expression_typedb Typing.PrintlnArgument e = true ->
  In (me, occ) (Index.occurrences_arg parent aidx pos e) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros e parent aidx pos me occ e' Ht Hin Hv. unfold Index.occurrences_arg in Hin.
  destruct (expression_typedb_const_info Typing.PrintlnArgument e Ht) as [ci Hci].
  exact (occurrences_expr_const_info_some e parent (Index.PrintlnArgument aidx) pos me occ e' ci Hci Hin Hv).
Qed.

Lemma occurrences_args_const_info_some : forall es parent aidx pos me occ e',
  forallb (expression_typedb Typing.PrintlnArgument) es = true ->
  In (me, occ) (Index.occurrences_args parent aidx pos es) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  induction es as [|e rest IH]; intros parent aidx pos me occ e' Ht Hin Hv;
    cbn [Index.occurrences_args] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hte Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occurrences_arg_const_info_some e parent aidx pos M O E Hte HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S aidx) (Pos.succ (Index.end_expr pos e)) M O E Htr HinM HvM).
Qed.

Lemma occurrences_stmt_const_info_some : forall s parent sidx pos me occ e',
  stmt_typedb s = true ->
  In (me, occ) (Index.occurrences_stmt parent sidx pos s) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros [args] parent sidx pos me occ e' Ht Hin Hv. cbn [Index.occurrences_stmt] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - cbn [Typing.stmt_typedb] in Ht.
    exact (occurrences_args_const_info_some args pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occurrences_stmts_const_info_some : forall ss parent sidx pos me occ e',
  forallb stmt_typedb ss = true ->
  In (me, occ) (Index.occurrences_stmts parent sidx pos ss) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  induction ss as [|s rest IH]; intros parent sidx pos me occ e' Ht Hin Hv;
    cbn [Index.occurrences_stmts] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hts Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occurrences_stmt_const_info_some s parent sidx pos M O E Hts HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S sidx) (Pos.succ (Index.end_stmt pos s)) M O E Htr HinM HvM).
Qed.

Lemma occurrences_decl_const_info_some : forall d parent didx pos me occ e',
  decl_typedb d = true ->
  In (me, occ) (Index.occurrences_decl parent didx pos d) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros [body] parent didx pos me occ e' Ht Hin Hv. cbn [Index.occurrences_decl] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - cbn [Typing.decl_typedb] in Ht.
    exact (occurrences_stmts_const_info_some body pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occurrences_decls_const_info_some : forall ds parent didx pos me occ e',
  forallb decl_typedb ds = true ->
  In (me, occ) (Index.occurrences_decls parent didx pos ds) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  induction ds as [|d rest IH]; intros parent didx pos me occ e' Ht Hin Hv;
    cbn [Index.occurrences_decls] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Htd Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occurrences_decl_const_info_some d parent didx pos M O E Htd HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S didx) (Pos.succ (Index.end_decl pos d)) M O E Htr HinM HvM).
Qed.

Lemma occurrences_file_const_info_some : forall f me occ e',
  source_file_typedb f = true ->
  In (me, occ) (Index.occurrences_file f) ->
  Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros f me occ e' Ht Hin Hv. unfold Index.occurrences_file in Hin.
  destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [Index.view_expr Index.occurrence_view] in Hv. discriminate Hv.
  - unfold Typing.source_file_typedb, file_typedb in Ht.
    exact (occurrences_decls_const_info_some (Syntax.declarations f) Index.root_id 0 (Pos.succ Index.package_id) me occ e' Ht Hin Hv).
Qed.

(* the WHOLE-PROGRAM statement: on [program_typedb] every visited expression occurrence's [constant_info] is [Some]. *)
Lemma program_visit_const_info_some (p : Syntax.Program) :
  program_typedb p = true ->
  forall r occ e', In (r, occ) (program_visit p) -> Index.view_expr occ = Some e' -> exists ci, constant_info e' = Some ci.
Proof.
  intros Hpt r occ e' Hin Hv. rewrite program_visit_flat_map in Hin. apply in_flat_map in Hin.
  destruct Hin as [b [Hb Hrb]]. unfold binding_visit in Hrb.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (Index.Snapshot.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc_at : Index.source_occurrence_at (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) = Some occ).
  { pose proof (Index.Snapshot.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply Index.occurrences_file_exact in Hsrc_at.
  unfold program_typedb in Hpt.
  pose proof (proj1 (forallb_forall (fun b => source_file_typedb (snd b))
                (Syntax.file_bindings (Syntax.files p))) Hpt b Hb) as Htb.
  cbv beta in Htb.
  assert (Hsrceq : snd b = Index.Snapshot.file_ref_source fr).
  { pose proof (Syntax.file_bindings_find (Syntax.files p) b Hb) as Hfb.
    pose proof (Index.Snapshot.file_of_path_source_exact p (fst b) fr Ef) as Hfe.
    rewrite Hfb in Hfe. injection Hfe as Heq; exact Heq. }
  rewrite Hsrceq in Htb.
  exact (occurrences_file_const_info_some (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) occ e' Htb Hsrc_at Hv).
Qed.

(* a NodeRef is ALWAYS visited (its file is represented, and [visit_file] is complete over the file). *)
Lemma noderef_in_prog_visit (p : Syntax.Program) (r : Index.Snapshot.NodeRef p) :
  In (r, Index.Snapshot.source_occurrence_of_ref r) (program_visit p).
Proof.
  pose proof (Index.Snapshot.file_of_path_complete p (Index.Snapshot.node_ref_file r)) as Hcomp.
  pose proof (Index.Snapshot.file_of_path_source_exact p
                (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file r))
                (Index.Snapshot.node_ref_file r) Hcomp) as Hfind.
  pose proof (Syntax.find_file_bindings (Syntax.files p)
                (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file r))
                (Index.Snapshot.file_ref_source (Index.Snapshot.node_ref_file r)) Hfind) as Hin_b.
  rewrite program_visit_flat_map. apply in_flat_map.
  exists (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file r),
          Index.Snapshot.file_ref_source (Index.Snapshot.node_ref_file r)).
  split; [exact Hin_b|]. unfold binding_visit; cbn [fst].
  rewrite Hcomp. apply Index.Snapshot.visit_file_complete. reflexivity.
Qed.

(* the conversion-child keys come off the delivered stream, with no separate source recursion *)

Definition operand_key {p} (r : Index.Snapshot.NodeRef p) : Index.Key :=
  Index.MakeKey (Index.key_path (Index.Snapshot.node_ref_key r)) (Pos.succ (Pos.succ (Index.Snapshot.node_ref_local r))).

(* a visited conversion's operand is itself visited, at the operand key *)
Lemma program_visit_operand (p : Syntax.Program) (idx : Index.Snapshot.Syntax p)
    (r : Index.Snapshot.NodeRef p) occ e x :
  In (r, occ) (program_visit p) -> Index.view_expr occ = Some e -> Typing.expression_child e = Some x ->
  exists r', In (r', Index.Snapshot.source_occurrence_of_ref r') (program_visit p)
    /\ Index.Snapshot.node_ref_key r' = operand_key r
    /\ Index.view_expr (Index.Snapshot.source_occurrence_of_ref r') = Some x
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref r') = Index.ConversionOperand.
Proof.
  intros Hin Hv Hc.
  rewrite program_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (Index.Snapshot.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc : Index.source_occurrence_at (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) = Some occ).
  { pose proof (Index.Snapshot.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply Index.occurrences_file_exact in Hsrc.
  destruct (occurrences_file_operand (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) occ e x Hsrc Hv Hc)
    as [occ' [Hin' [Hvx Hrole]]].
  apply Index.occurrences_file_exact in Hin'.
  assert (Hvalid : Index.valid_localb (Index.Snapshot.file_ref_source fr) (Pos.succ (Pos.succ (Index.Snapshot.node_ref_local r))) = true).
  { unfold Index.valid_localb.
    rewrite (Index.source_occurrence_meta (Index.Snapshot.file_ref_source fr)
               (Pos.succ (Pos.succ (Index.Snapshot.node_ref_local r))) occ' Hin'). reflexivity. }
  pose proof (Index.Snapshot.file_of_path_source_exact p (fst b) fr Ef) as Hfind.
  pose proof (Index.Snapshot.file_of_path_sound p (fst b) fr Ef) as Hpath.
  assert (Hfind' : Syntax.find_file (Index.Snapshot.file_ref_path fr) (Syntax.files p) = Some (Index.Snapshot.file_ref_source fr))
    by (rewrite Hpath; exact Hfind).
  destruct (Index.Snapshot.ref_of_key_source p idx
              (Index.Snapshot.file_ref_path fr) (Index.Snapshot.file_ref_source fr)
              (Pos.succ (Pos.succ (Index.Snapshot.node_ref_local r))) Hfind' Hvalid) as [r' [Hrok [Hrlocal Hrsrc]]].
  exists r'.
  assert (Hkey : Index.Snapshot.node_ref_key r' = operand_key r).
  { pose proof (Index.Snapshot.ref_of_key_sound p idx _ r' Hrok) as Hk.
    rewrite Hk. unfold operand_key. rewrite Index.Snapshot.node_ref_key_eq. cbn [Index.key_path]. rewrite Hfile. reflexivity. }
  assert (Hsor : Index.Snapshot.source_occurrence_of_ref r' = occ').
  { pose proof (Index.Snapshot.source_occ_of_ref_eq r') as Hso'.
    rewrite Hrlocal, Hrsrc in Hso'.
    rewrite Hin' in Hso'. injection Hso' as ->. reflexivity. }
  split; [ | split; [ | split ] ].
  - apply noderef_in_prog_visit.
  - exact Hkey.
  - rewrite Hsor; exact Hvx.
  - rewrite Hsor; exact Hrole.
Qed.

(* a conversion's type-name occurrence sits at the target child key *)
Definition type_name_key {p} (r : Index.Snapshot.NodeRef p) : Index.Key :=
  Index.MakeKey (Index.key_path (Index.Snapshot.node_ref_key r)) (Pos.succ (Index.Snapshot.node_ref_local r)).

(* the target child key is injective in the conversion's own key, so identity is by occurrence *)
Lemma type_name_key_inj {p} (r1 r2 : Index.Snapshot.NodeRef p) :
  type_name_key r1 = type_name_key r2 -> Index.Snapshot.node_ref_key r1 = Index.Snapshot.node_ref_key r2.
Proof.
  unfold type_name_key. rewrite !Index.Snapshot.node_ref_key_eq. cbn [Index.key_path].
  intro H. injection H as Hf Hl. apply Pos.succ_inj in Hl. rewrite Hf, Hl. reflexivity.
Qed.

(* a visited conversion's type name is itself visited, recovering the exact source syntax *)
Lemma program_visit_type_name (p : Syntax.Program) (idx : Index.Snapshot.Syntax p)
    (r : Index.Snapshot.NodeRef p) occ ts x :
  In (r, occ) (program_visit p) -> Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists r', In (r', Index.Snapshot.source_occurrence_of_ref r') (program_visit p)
    /\ Index.Snapshot.node_ref_key r' = type_name_key r
    /\ Index.view_typename (Index.Snapshot.source_occurrence_of_ref r') = Some ts
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref r') = Index.ConversionTarget.
Proof.
  intros Hin Hv.
  rewrite program_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (Index.Snapshot.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc : Index.source_occurrence_at (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) = Some occ).
  { pose proof (Index.Snapshot.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply Index.occurrences_file_exact in Hsrc.
  destruct (occurrences_file_type_name (Index.Snapshot.file_ref_source fr) (Index.Snapshot.node_ref_local r) occ ts x Hsrc Hv)
    as [occ' [Hin' Hvts]].
  pose proof (occurrences_file_typename_role (Index.Snapshot.file_ref_source fr)
                (Pos.succ (Index.Snapshot.node_ref_local r)) occ' ts Hin' Hvts) as Hrole.
  apply Index.occurrences_file_exact in Hin'.
  assert (Hvalid : Index.valid_localb (Index.Snapshot.file_ref_source fr) (Pos.succ (Index.Snapshot.node_ref_local r)) = true).
  { unfold Index.valid_localb.
    rewrite (Index.source_occurrence_meta (Index.Snapshot.file_ref_source fr)
               (Pos.succ (Index.Snapshot.node_ref_local r)) occ' Hin'). reflexivity. }
  pose proof (Index.Snapshot.file_of_path_source_exact p (fst b) fr Ef) as Hfind.
  pose proof (Index.Snapshot.file_of_path_sound p (fst b) fr Ef) as Hpath.
  assert (Hfind' : Syntax.find_file (Index.Snapshot.file_ref_path fr) (Syntax.files p) = Some (Index.Snapshot.file_ref_source fr))
    by (rewrite Hpath; exact Hfind).
  destruct (Index.Snapshot.ref_of_key_source p idx
              (Index.Snapshot.file_ref_path fr) (Index.Snapshot.file_ref_source fr)
              (Pos.succ (Index.Snapshot.node_ref_local r)) Hfind' Hvalid) as [r' [Hrok [Hrlocal Hrsrc]]].
  exists r'.
  assert (Hkey : Index.Snapshot.node_ref_key r' = type_name_key r).
  { pose proof (Index.Snapshot.ref_of_key_sound p idx _ r' Hrok) as Hk.
    rewrite Hk. unfold type_name_key. rewrite Index.Snapshot.node_ref_key_eq. cbn [Index.key_path]. rewrite Hfile. reflexivity. }
  assert (Hsor : Index.Snapshot.source_occurrence_of_ref r' = occ').
  { pose proof (Index.Snapshot.source_occ_of_ref_eq r') as Hso'.
    rewrite Hrlocal, Hrsrc in Hso'.
    rewrite Hin' in Hso'. injection Hso' as ->. reflexivity. }
  split; [ | split; [ | split ] ].
  - apply noderef_in_prog_visit.
  - exact Hkey.
  - rewrite Hsor; exact Hvts.
  - rewrite Hsor; exact Hrole.
Qed.

(* a conversion's exact target reference, minted through the retained index *)
Definition conversion_target_ref {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p)
  : option (Index.TypeNameRef p) :=
  match Index.Snapshot.ref_of_key p idx (type_name_key (Index.erase_ref er)) with
  | Some r => Index.as_type_name idx r
  | None => None
  end.

Lemma conversion_target_ref_conv {p} (idx : Index.Snapshot.Syntax p)
    (r : Index.Snapshot.NodeRef p) occ (er : Index.ExprRef p) ts x :
  In (r, occ) (program_visit p) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  Index.as_expr idx r = Some er ->
  exists tr, conversion_target_ref idx er = Some tr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr) = type_name_key r
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr)) = Index.ConversionTarget
    /\ Index.type_name_ref_syntax tr = Some ts.
Proof.
  intros Hin Hv Hae.
  pose proof (Index.erase_as_kind idx r Index.ExpressionKind er Hae) as Her.
  destruct (program_visit_type_name p idx r occ ts x Hin Hv) as [r' [Hin' [Hkey [Hvts Hrole]]]].
  assert (Hkind : Index.Snapshot.node_kind idx r' = Index.TypeNameKind).
  { rewrite (Index.Snapshot.node_kind_matches_source p idx r'). exact (Index.view_typename_kind _ ts Hvts). }
  destruct (Index.as_kind_complete idx r' Index.TypeNameKind Hkind) as [tr [Hastr Hetr]].
  exists tr.
  assert (Hcompute : conversion_target_ref idx er = Some tr).
  { unfold conversion_target_ref. rewrite Her, <- Hkey, Index.Snapshot.ref_of_key_complete.
    unfold Index.as_type_name. exact Hastr. }
  split; [ exact Hcompute | ].
  split; [ rewrite Hetr; exact Hkey | ].
  split; [ rewrite Hetr; exact Hrole | ].
  unfold Index.type_name_ref_syntax. rewrite Hetr. exact Hvts.
Qed.

(* a conversion's exact operand reference, the mirror of its target *)
Definition conversion_operand_ref {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p)
  : option (Index.ExprRef p) :=
  match Index.Snapshot.ref_of_key p idx (operand_key (Index.erase_ref er)) with
  | Some r => Index.as_expr idx r
  | None => None
  end.

Lemma conversion_operand_ref_conv {p} (idx : Index.Snapshot.Syntax p)
    (r : Index.Snapshot.NodeRef p) occ (er : Index.ExprRef p) ts x :
  In (r, occ) (program_visit p) ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  Index.as_expr idx r = Some er ->
  exists opr, conversion_operand_ref idx er = Some opr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref opr) = operand_key r
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) = Index.ConversionOperand
    /\ Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) = Some x.
Proof.
  intros Hin Hv Hae.
  pose proof (Index.erase_as_kind idx r Index.ExpressionKind er Hae) as Her.
  destruct (program_visit_operand p idx r occ (Syntax.Convert ts x) x Hin Hv eq_refl) as [r' [Hin' [Hkey [Hvx Hrole]]]].
  assert (Hkind : Index.Snapshot.node_kind idx r' = Index.ExpressionKind).
  { rewrite (Index.Snapshot.node_kind_matches_source p idx r'). exact (Index.view_expr_kind _ x Hvx). }
  destruct (Index.as_kind_complete idx r' Index.ExpressionKind Hkind) as [opr [Haopr Heopr]].
  exists opr.
  assert (Hcompute : conversion_operand_ref idx er = Some opr).
  { unfold conversion_operand_ref. rewrite Her, <- Hkey, Index.Snapshot.ref_of_key_complete.
    unfold Index.as_expr. exact Haopr. }
  split; [ exact Hcompute | ].
  split; [ rewrite Heopr; exact Hkey | ].
  split; [ rewrite Heopr; exact Hrole | ].
  rewrite Heopr; exact Hvx.
Qed.

(* a reference refines its own erased node, decided by key rather than by proof irrelevance *)
Lemma as_expr_erase {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) :
  Index.as_expr idx (Index.erase_ref er) = Some er.
Proof.
  assert (Hk : Index.Snapshot.node_kind idx (Index.erase_ref er) = Index.ExpressionKind).
  { rewrite (Index.Snapshot.node_kind_matches_source p idx (Index.erase_ref er)). exact (Index.noderefof_kind er). }
  destruct (Index.as_kind_complete idx (Index.erase_ref er) Index.ExpressionKind Hk) as [er' [Ha He']].
  unfold Index.as_expr. rewrite Ha. f_equal. apply Index.noderefof_key_inj. rewrite He'. reflexivity.
Qed.

(* the typed conversion children, minted from the reference's own source view *)
Lemma conversion_target_ref_of_view {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x) ->
  exists tr, conversion_target_ref idx er = Some tr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr) = type_name_key (Index.erase_ref er)
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr)) = Index.ConversionTarget
    /\ Index.type_name_ref_syntax tr = Some ts.
Proof.
  intro Hview.
  exact (conversion_target_ref_conv idx (Index.erase_ref er) (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er))
           er ts x (noderef_in_prog_visit p (Index.erase_ref er)) Hview (as_expr_erase idx er)).
Qed.

Lemma conversion_operand_ref_of_view {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x) ->
  exists opr, conversion_operand_ref idx er = Some opr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref opr) = operand_key (Index.erase_ref er)
    /\ Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) = Index.ConversionOperand
    /\ Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) = Some x.
Proof.
  intro Hview.
  exact (conversion_operand_ref_conv idx (Index.erase_ref er) (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er))
           er ts x (noderef_in_prog_visit p (Index.erase_ref er)) Hview (as_expr_erase idx er)).
Qed.

Lemma conversion_target_ref_not_none {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x) ->
  conversion_target_ref idx er <> None.
Proof. intro Hv. destruct (conversion_target_ref_of_view idx er ts x Hv) as [tr [Hc _]]. rewrite Hc. discriminate. Qed.

Lemma conversion_operand_ref_not_none {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x) ->
  conversion_operand_ref idx er <> None.
Proof. intro Hv. destruct (conversion_operand_ref_of_view idx er ts x Hv) as [opr [Hc _]]. rewrite Hc. discriminate. Qed.

(* the total projection of a proved-non-[None] option, discharging the impossible branch by that same proof *)
Definition from_some {A} (o : option A) (H : o <> None) : A :=
  match o return o <> None -> A with Some a => fun _ => a | None => fun H0 => False_rect A (H0 eq_refl) end H.
Lemma from_some_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> from_some o H = a.
Proof. intro Heq. subst o. reflexivity. Qed.
Lemma from_some_some {A} (o : option A) (H : o <> None) : o = Some (from_some o H).
Proof. destruct o as [a|]; [reflexivity | exfalso; apply H; reflexivity]. Qed.
(* the projection depends only on the option, so two non-emptiness proofs give the same result *)
Lemma from_some_pi {A} (o : option A) (H1 H2 : o <> None) : from_some o H1 = from_some o H2.
Proof. destruct o as [a|]; [reflexivity | destruct (H1 eq_refl)]. Qed.
(* equal options give equal projections (the witnesses are irrelevant). *)
Lemma from_some_congr {A} (o1 o2 : option A) (H1 : o1 <> None) (H2 : o2 <> None) :
  o1 = o2 -> from_some o1 H1 = from_some o2 H2.
Proof. intro Ho. revert H2. rewrite <- Ho. intro H2. apply from_some_pi. Qed.

(* on the live path a conversion's children are obtained through the index with no [None] fallback *)
Definition conversion_target_ref_tot {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x
    (Hv : Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x))
  : Index.TypeNameRef p :=
  from_some (conversion_target_ref idx er) (conversion_target_ref_not_none idx er ts x Hv).
Definition conversion_operand_ref_tot {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x
    (Hv : Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (Syntax.Convert ts x))
  : Index.ExprRef p :=
  from_some (conversion_operand_ref idx er) (conversion_operand_ref_not_none idx er ts x Hv).

Lemma conversion_target_ref_tot_eq {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x Hv tr :
  conversion_target_ref idx er = Some tr -> conversion_target_ref_tot idx er ts x Hv = tr.
Proof. intro Heq. unfold conversion_target_ref_tot. apply from_some_eq. exact Heq. Qed.
Lemma conversion_operand_ref_tot_eq {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x Hv opr :
  conversion_operand_ref idx er = Some opr -> conversion_operand_ref_tot idx er ts x Hv = opr.
Proof. intro Heq. unfold conversion_operand_ref_tot. apply from_some_eq. exact Heq. Qed.

(* the total children recover the exact operand and the exact source type syntax *)
Lemma conversion_operand_ref_tot_view {p} (idx : Index.Snapshot.Syntax p) (er : Index.ExprRef p) ts x Hv :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref (conversion_operand_ref_tot idx er ts x Hv))) = Some x.
Proof.
  destruct (conversion_operand_ref_of_view idx er ts x Hv) as [opr [Hc [_ [_ Hview]]]].
  rewrite (conversion_operand_ref_tot_eq idx er ts x Hv opr Hc). exact Hview.
Qed.

(* the one place a conversion's status is reduced to expose its operand's, without expanding that operand *)
Lemma const_info_conv_eq : forall ts x,
  constant_info (Syntax.Convert ts x)
  = match constant_info x with
    | Some ci => option_map (Typing.TypedInfo (predeclared_type ts)) (Typing.convert_constant (predeclared_type ts) ci)
    | None => None
    end.
Proof. intros ts x. reflexivity. Qed.

(* a type-name fact stores the resolved type only, so the alias pairs stay distinct sources with equal facts *)

Record TypeNameFact : Type := MakeTypeNameFact { fact_type : Typing.SemanticType }.

(* one occurrence's type-name fact, resolving its retained source syntax through the predeclared context *)
Definition occurrence_type_name_fact (o : Index.Occurrence) : option TypeNameFact :=
  match Index.view_typename o with
  | Some ts => Some (MakeTypeNameFact (predeclared_type ts))
  | None => None
  end.

Lemma occurrence_type_name_fact_some : forall o ts,
  Index.view_typename o = Some ts -> occurrence_type_name_fact o = Some (MakeTypeNameFact (predeclared_type ts)).
Proof. intros o ts H. unfold occurrence_type_name_fact. rewrite H. reflexivity. Qed.
Lemma occurrence_type_name_fact_none : forall o,
  Index.view_typename o = None -> occurrence_type_name_fact o = None.
Proof. intros o H. unfold occurrence_type_name_fact. rewrite H. reflexivity. Qed.

Definition add_tn_fact {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
    (m : Index.KeyMap.t TypeNameFact) : Index.KeyMap.t TypeNameFact :=
  match occurrence_type_name_fact (snd ro) with
  | Some f => Index.KeyMap.add (Index.Snapshot.node_ref_key (fst ro)) f m
  | None => m
  end.

Lemma type_name_facts_not_in_domain {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) (k : Index.Key) :
  ~ In k (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) l) ->
  Index.KeyMap.find k (fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) l) = None.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hni; simpl.
  - apply Index.KeyFacts.empty_o.
  - simpl in Hni.
    assert (Hne : Index.Snapshot.node_ref_key r0 <> k) by (intro H; apply Hni; left; exact H).
    assert (Hrest : ~ In k (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) rest))
      by (intro H; apply Hni; right; exact H).
    unfold add_tn_fact; cbn [snd fst]. destruct (occurrence_type_name_fact occ0) as [f|].
    + rewrite Index.key_map_add_unequal by exact Hne. exact (IH Hrest).
    + exact (IH Hrest).
Qed.

Lemma type_name_fold_facts_find {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) r occ :
  NoDup (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) l) ->
  In (r, occ) l ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r)
    (fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) l) = occurrence_type_name_fact occ.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hnd Hin; [ destruct Hin |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  simpl. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. unfold add_tn_fact; cbn [snd fst].
    destruct (occurrence_type_name_fact occ0) as [f|] eqn:Ef.
    + rewrite Index.key_map_add_equal. reflexivity.
    + apply type_name_facts_not_in_domain. exact Hni.
  - assert (Hin' : In (Index.Snapshot.node_ref_key r)
             (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) rest)).
    { apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hin]. }
    assert (Hkr : Index.Snapshot.node_ref_key r <> Index.Snapshot.node_ref_key r0)
      by (intro Hk; apply Hni; rewrite <- Hk; exact Hin').
    unfold add_tn_fact; cbn [snd fst]. destruct (occurrence_type_name_fact occ0) as [f0|].
    + rewrite Index.key_map_add_unequal by (intro Hk; apply Hkr; symmetry; exact Hk).
      exact (IH Hnd' Hin).
    + exact (IH Hnd' Hin).
Qed.

Lemma type_name_fold_facts_domain {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) k f :
  Index.KeyMap.find k (fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) l) = Some f ->
  exists ro, In ro l /\ Index.Snapshot.node_ref_key (fst ro) = k /\ occurrence_type_name_fact (snd ro) = Some f.
Proof.
  induction l as [|ro rest IH]; intro Hf.
  - rewrite Index.KeyFacts.empty_o in Hf; discriminate Hf.
  - cbn [fold_right] in Hf. unfold add_tn_fact in Hf.
    destruct (occurrence_type_name_fact (snd ro)) as [f0|] eqn:Ef.
    + destruct (Index.key_eq_dec (Index.Snapshot.node_ref_key (fst ro)) k) as [He|Hne].
      * subst k. rewrite Index.key_map_add_equal in Hf. injection Hf as <-.
        exists ro. split; [left; reflexivity | split; [reflexivity | exact Ef]].
      * rewrite Index.key_map_add_unequal in Hf by exact Hne.
        destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
    + destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Definition program_type_name_facts (p : Syntax.Program) : Index.KeyMap.t TypeNameFact :=
  fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) (program_visit p).

Lemma program_type_name_facts_find (p : Syntax.Program) (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (program_visit p) ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r) (program_type_name_facts p) = occurrence_type_name_fact occ.
Proof. intro Hin. apply type_name_fold_facts_find; [ apply program_visit_key_nodup | exact Hin ]. Qed.

Lemma program_type_name_facts_domain (p : Syntax.Program) k f :
  Index.KeyMap.find k (program_type_name_facts p) = Some f ->
  exists (r : Index.Snapshot.NodeRef p) occ, In (r, occ) (program_visit p)
    /\ Index.Snapshot.node_ref_key r = k /\ occurrence_type_name_fact occ = Some f.
Proof.
  intro Hf. destruct (type_name_fold_facts_domain (program_visit p) k f Hf) as [[r occ] [Hin [Hk Hfe]]].
  exists r, occ. cbn [fst snd] in *. split; [exact Hin | split; [exact Hk | exact Hfe]].
Qed.

(** the sealed type-name table: its keys are exactly the visited type-name occurrences, each fact exact *)
Record TypeNameFacts (p : Syntax.Program) : Type := MakeTypeNameFacts {
  type_name_map      : Index.KeyMap.t TypeNameFact ;
  type_name_domain   : forall k f, Index.KeyMap.find k type_name_map = Some f ->
                    exists (r : Index.Snapshot.NodeRef p) occ, In (r, occ) (program_visit p)
                      /\ Index.Snapshot.node_ref_key r = k /\ occurrence_type_name_fact occ = Some f ;
  type_name_complete : forall r occ, In (r, occ) (program_visit p) ->
                    Index.KeyMap.find (Index.Snapshot.node_ref_key r) type_name_map = occurrence_type_name_fact occ
}.
Arguments MakeTypeNameFacts {p} _ _ _.
Arguments type_name_map {p} _.
Arguments type_name_domain {p} _.
Arguments type_name_complete {p} _.

(** the table-level total query projects a stored entry; totality comes from the table's own proof *)
Lemma type_name_table_not_none {p} (tnft : TypeNameFacts p) (tr : Index.TypeNameRef p) :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map tnft) <> None.
Proof.
  destruct (Index.kind_view_typename _ (Index.noderefof_kind tr)) as [ts Hv].
  rewrite (type_name_complete tnft (Index.erase_ref tr) (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr))
             (noderef_in_prog_visit p (Index.erase_ref tr))).
  rewrite (occurrence_type_name_fact_some _ ts Hv). discriminate.
Qed.
Definition type_name_fact_at_table {p} (tnft : TypeNameFacts p) (tr : Index.TypeNameRef p) : TypeNameFact :=
  from_some (Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map tnft))
            (type_name_table_not_none tnft tr).
Lemma type_name_fact_at_table_find {p} (tnft : TypeNameFacts p) (tr : Index.TypeNameRef p) f :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map tnft) = Some f ->
  type_name_fact_at_table tnft tr = f.
Proof. intro Hf. unfold type_name_fact_at_table. apply from_some_eq. exact Hf. Qed.
Lemma type_name_fact_at_table_resolves {p} (tnft : TypeNameFacts p) (tr : Index.TypeNameRef p) ts :
  Index.type_name_ref_syntax tr = Some ts -> type_name_fact_at_table tnft tr = MakeTypeNameFact (predeclared_type ts).
Proof.
  intro Hts. unfold Index.type_name_ref_syntax in Hts. apply type_name_fact_at_table_find.
  rewrite (type_name_complete tnft (Index.erase_ref tr) (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr))
             (noderef_in_prog_visit p (Index.erase_ref tr))).
  exact (occurrence_type_name_fact_some _ ts Hts).
Qed.

(* a conversion's operand is a later preorder node, so its outcome is already in the accumulator *)
Lemma strongly_sorted_prefix_lt {A} (R : A -> A -> Prop) (a : list A) (v : A) (b : list A) :
  StronglySorted R (a ++ v :: b) -> Forall (fun z => R z v) a.
Proof.
  induction a as [|y a IH]; intro Hss; [constructor|].
  cbn [app] in Hss. apply StronglySorted_inv in Hss. destruct Hss as [Hss Hall].
  constructor; [ rewrite Forall_forall in Hall; apply Hall, in_or_app; right; left; reflexivity | apply IH; exact Hss ].
Qed.

Lemma strongly_sorted_after_local {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) P y S :
  StronglySorted Pos.lt (map (fun rc => Index.Snapshot.node_ref_local (fst rc)) l) ->
  l = P ++ y :: S ->
  forall z, In z l -> (Index.Snapshot.node_ref_local (fst y) < Index.Snapshot.node_ref_local (fst z))%positive -> In z S.
Proof.
  intros Hss Hsplit z Hz Hlt. subst l. rewrite map_app in Hss. cbn [map] in Hss.
  pose proof (strongly_sorted_prefix_lt _ (map (fun rc => Index.Snapshot.node_ref_local (fst rc)) P)
                (Index.Snapshot.node_ref_local (fst y))
                (map (fun rc => Index.Snapshot.node_ref_local (fst rc)) S) Hss) as Hpre.
  apply in_app_or in Hz. destruct Hz as [HzP | [Hzy | HzS]].
  - exfalso. rewrite Forall_forall in Hpre.
    assert (Hzin : In (Index.Snapshot.node_ref_local (fst z)) (map (fun rc => Index.Snapshot.node_ref_local (fst rc)) P))
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

Lemma program_visit_not_in_prefix {p} (L : list (Index.Snapshot.NodeRef p * Index.Occurrence)) l1 r occ l2 :
  NoDup (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) L) -> L = l1 ++ (r, occ) :: l2 -> ~ In (r, occ) l1.
Proof.
  intros Hnd HL Hbad. rewrite HL, map_app in Hnd. cbn [map fst] in Hnd.
  apply NoDup_remove_2 in Hnd. apply Hnd, in_or_app. left.
  apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hbad].
Qed.

Lemma program_visit_operand_closed (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) :
  forall l1 r occ l2, program_visit p = l1 ++ (r, occ) :: l2 ->
    forall e x, Index.view_expr occ = Some e -> Typing.expression_child e = Some x ->
    exists r' occ', Index.Snapshot.node_ref_key r' = operand_key r /\ Index.view_expr occ' = Some x /\ In (r', occ') l2.
Proof.
  intros l1 r occ l2 Hsplit e x Hv Hc.
  assert (Hin_ro : In (r, occ) (program_visit p)) by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  destruct (program_visit_operand p idx r occ e x Hin_ro Hv Hc) as [r' [Hin'p [Hkey [Hvx _]]]].
  exists r', (Index.Snapshot.source_occurrence_of_ref r'). split; [exact Hkey | split; [exact Hvx |]].
  pose proof Hin_ro as Hb0. rewrite program_visit_flat_map in Hb0. apply in_flat_map in Hb0. destruct Hb0 as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (Index.Snapshot.visit_file_view p fr r occ Hrb) as [_ Hfile].
  pose proof (Index.Snapshot.node_ref_key_eq r') as Hk'. rewrite Hkey in Hk'. unfold operand_key in Hk'.
  rewrite Index.Snapshot.node_ref_key_eq in Hk'. cbn [Index.key_path] in Hk'. rewrite Hfile in Hk'.
  injection Hk' as Hpatheq Hloceq.
  assert (Hfile' : Index.Snapshot.node_ref_file r' = fr) by (apply Index.Snapshot.file_ref_path_inj; symmetry; exact Hpatheq).
  pose proof (Index.Snapshot.visit_file_complete p fr r' Hfile') as Hin'block.
  apply in_split in Hrb. destruct Hrb as [P [S Hvfsplit]].
  assert (Hin'S : In (r', Index.Snapshot.source_occurrence_of_ref r') S).
  { apply (strongly_sorted_after_local (Index.Snapshot.visit_file fr) P (r, occ) S (Index.Snapshot.visit_file_order p fr) Hvfsplit
             (r', Index.Snapshot.source_occurrence_of_ref r') Hin'block).
    cbn [fst]. rewrite <- Hloceq. lia. }
  apply in_split in Hb. destruct Hb as [B1 [B2 Hbsplit]].
  assert (Hbv : binding_visit p b = Index.Snapshot.visit_file fr) by (unfold binding_visit; rewrite Ef; reflexivity).
  assert (Hpv : program_visit p = (flat_map (binding_visit p) B1 ++ P) ++ (r, occ) :: (S ++ flat_map (binding_visit p) B2)).
  { rewrite program_visit_flat_map, Hbsplit, flat_map_app. cbn [flat_map]. rewrite Hbv, Hvfsplit.
    rewrite <- !app_assoc. reflexivity. }
  pose proof (program_visit_key_nodup p) as Hnd.
  assert (Hl2 : l2 = S ++ flat_map (binding_visit p) B2).
  { apply (split_unique (r, occ) l1 l2 (flat_map (binding_visit p) B1 ++ P) (S ++ flat_map (binding_visit p) B2)).
    - rewrite <- Hsplit. exact Hpv.
    - exact (program_visit_not_in_prefix (program_visit p) l1 r occ l2 Hnd Hsplit).
    - exact (program_visit_not_in_prefix (program_visit p) (flat_map (binding_visit p) B1 ++ P) r occ
               (S ++ flat_map (binding_visit p) B2) Hnd Hpv). }
  rewrite Hl2. apply in_or_app. left. exact Hin'S.
Qed.

(* the one proof-carrying bottom-up accumulator, folded over the retained source-order visit *)
Definition expression_ref_role {p} (er : Index.ExprRef p) : Index.Role :=
  Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)).

(* one conversion's outcome from its target-Index.table query + operand outcome — ONE Typing.convert_constant. *)
Definition conv_outcome {p} (tnft : TypeNameFacts p) (er : Index.ExprRef p)
    (tr : Index.TypeNameRef p) (opr : Index.ExprRef p) (oo : ExpressionOutcome p) : ExpressionOutcome p :=
  match oo with
  | ExpressionSuccess opf =>
      match Typing.convert_constant (fact_type (type_name_fact_at_table tnft tr)) (const_status opf) with
      | Some tc => ExpressionSuccess (MakeExpressionFact (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft tr)) tc)
                          (use_resolved_of_input (expression_ref_role er)
                             (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft tr)) tc)))
      | None    => ConversionFailure er tr opr (fact_type (type_name_fact_at_table tnft tr)) (const_status opf)
      end
  | _ => ChildFailure
  end.

(* a LEAF's constant — NO fake [Syntax.Convert] case (a dependent proof the constructor is a leaf). *)
Lemma expression_child_leaf_absurd (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Typing.expression_child (Syntax.Convert ts x) = None -> False.
Proof. cbn [Typing.expression_child]. discriminate. Qed.
Definition leaf_const (e : Syntax.Expr) : Typing.expression_child e = None -> Typing.ConstantInfo :=
  match e return Typing.expression_child e = None -> Typing.ConstantInfo with
  | Syntax.BoolLiteral b     => fun _ => Typing.UntypedInfo (Typing.BoolConstant b)
  | Syntax.IntegerLiteral n      => fun _ => Typing.UntypedInfo (Typing.IntegerConstant (Z.of_N n))
  | Syntax.NegatedIntegerLiteral n      => fun _ => Typing.UntypedInfo (Typing.IntegerConstant (- Z.of_N n))
  | Syntax.StringLiteral s   => fun _ => Typing.UntypedInfo (Typing.StringConstant s)
  | Syntax.FloatLiteral d    => fun _ => Typing.UntypedInfo (Typing.FloatConstant (Float.decimal_value d))
  | Syntax.ComplexLiteral dc => fun _ => Typing.UntypedInfo (Typing.ComplexConstant (Complex.decimal_value dc))
  | Syntax.Convert ts x => fun H => False_rect Typing.ConstantInfo (expression_child_leaf_absurd ts x H)
  end.
Lemma leaf_const_status (e : Syntax.Expr) (H : Typing.expression_child e = None) : constant_info e = Some (leaf_const e H).
Proof. destruct e as [ b|n|n0|s|d|dc| ts x ]; try reflexivity. exfalso. exact (expression_child_leaf_absurd ts x H). Qed.

(* a leaf occurrence's outcome — its untyped fact + its use-context resolution from that same status. *)
Definition leaf_outcome {p} (er : Index.ExprRef p) (ci : Typing.ConstantInfo) : ExpressionOutcome p :=
  ExpressionSuccess (MakeExpressionFact ci (use_resolved_of_input (expression_ref_role er) ci)).

(** a conversion whose operand succeeded but whose own step failed, carrying target and operand status *)
Definition local_conv_failure (e : Syntax.Expr) : option (Typing.SemanticType * Typing.ConstantInfo) :=
  match e with
  | Syntax.Convert ts x =>
      match constant_info x with
      | Some ci => match Typing.convert_constant (predeclared_type ts) ci with
                   | None => Some (predeclared_type ts, ci) | Some _ => None end
      | None => None end
  | _ => None
  end.

(** every retained member's stored outcome matches its occurrence, projected from the retained trace *)
Definition outcome_convfail_ev {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p)
    (occ : Index.Occurrence) (er2 : Index.ExprRef p) (tr2 : Index.TypeNameRef p)
    (opr2 : Index.ExprRef p) (t : Typing.SemanticType) (ci : Typing.ConstantInfo) : Prop :=
  Index.as_expr idx r = Some er2
  /\ (exists e, Index.view_expr occ = Some e /\ local_conv_failure e = Some (t, ci))
  /\ conversion_target_ref idx er2 = Some tr2
  /\ conversion_operand_ref idx er2 = Some opr2.

Definition outcome_matches {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p)
    (occ : Index.Occurrence) (out : ExpressionOutcome p) : Prop :=
  match out with
  | ExpressionSuccess f => occurrence_expr_fact occ = Some f
  | ConversionFailure er2 tr2 opr2 t ci => occurrence_expr_fact occ = None /\ outcome_convfail_ev idx r occ er2 tr2 opr2 t ci
  (* the operand failed, so the diagnostic anchors at the operand rather than at this conversion *)
  | ChildFailure => occurrence_expr_fact occ = None /\ (exists e, Index.view_expr occ = Some e /\ local_conv_failure e = None)
  end.

(* the FACT-only projection (facts layer): an ExpressionSuccess fact is exact, any other outcome has no fact. *)
Definition outcome_proj_fact {p} (out : ExpressionOutcome p) (occ : Index.Occurrence) : Prop :=
  match out with
  | ExpressionSuccess f => occurrence_expr_fact occ = Some f
  | _      => occurrence_expr_fact occ = None
  end.

Lemma outcome_matches_proj {p} (idx : Index.Snapshot.Syntax p) r occ (out : ExpressionOutcome p) :
  outcome_matches idx r occ out -> outcome_proj_fact out occ.
Proof. destruct out as [f|? ? ? ? ?| ]; cbn [outcome_matches outcome_proj_fact]; intro H; [exact H | exact (proj1 H) | exact (proj1 H)]. Qed.

(** the retained compilation input: the index, the per-file blocks and their flattened visit, all stored *)
Record Input (p : Syntax.Program) : Type := MakeInput {
  indexed     : Index.Program p ;
  input_blocks : list (list (Index.Snapshot.NodeRef p * Index.Occurrence)) ;
  input_visit  : list (Index.Snapshot.NodeRef p * Index.Occurrence) ;   (* STORED once, consumed by every builder *)
  input_blocks_ok    : input_blocks = program_blocks p ;   (* PROVENANCE (spec): the stored blocks ARE the snapshot's *)
  input_visit_blocks : input_visit  = concat input_blocks  (* COHERENCE: the stored visit IS its blocks' flattening *)
}.
Arguments MakeInput {p} _ _ _ _ _.
Arguments indexed {p} _.  Arguments input_blocks {p} _.  Arguments input_visit {p} _.
Arguments input_blocks_ok {p} _.  Arguments input_visit_blocks {p} _.

Definition index {p} (input : Input p) : Index.Snapshot.Syntax p :=
  Index.indexed_syntax (indexed input).

(* the stored visit is the snapshot's canonical one, as data rather than a re-flattening *)
Lemma input_visit_ok {p} (input : Input p) : input_visit input = program_visit p.
Proof. unfold program_visit. rewrite (input_visit_blocks input), (input_blocks_ok input). reflexivity. Qed.

(* the sole traversal: the file-visit blocks are computed once and everything downstream reads them *)
Definition build_compilation_input (p : Syntax.Program) (ip : Index.Program p) : Input p :=
  let blocks := program_blocks p in
  MakeInput ip blocks (concat blocks) eq_refl eq_refl.

(* a non-success outcome, which is what a child-failure cause carries about its operand *)
Definition outcome_is_fail {p} (o : ExpressionOutcome p) : Prop :=
  match o with ExpressionSuccess _ => False | _ => True end.

(* every present key is a visited expression occurrence's, excluding both a wrong-kind and a foreign key *)
Definition outcome_dom_exact {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence))
    (m : Index.KeyMap.t (ExpressionOutcome p)) : Prop :=
  forall k, Index.KeyMap.find k m <> None ->
    exists (r : Index.Snapshot.NodeRef p) occ e,
      In (r, occ) l /\ Index.Snapshot.node_ref_key r = k /\ Index.view_expr occ = Some e.

Lemma outcome_dom_exact_empty {p} :
  outcome_dom_exact (@nil (Index.Snapshot.NodeRef p * Index.Occurrence)) (Index.KeyMap.empty (ExpressionOutcome p)).
Proof. intros k Hk. exfalso. apply Hk. apply Index.KeyFacts.empty_o. Qed.

Lemma outcome_dom_exact_skip {p} (r : Index.Snapshot.NodeRef p) (occ : Index.Occurrence)
    (rest : list (Index.Snapshot.NodeRef p * Index.Occurrence)) m_rest :
  outcome_dom_exact rest m_rest -> outcome_dom_exact ((r, occ) :: rest) m_rest.
Proof.
  intros Hdom k Hk. destruct (Hdom k Hk) as [r0 [occ0 [e0 [Hin0 [Hk0 Hv0]]]]].
  exists r0, occ0, e0. split; [right; exact Hin0 | split; [ exact Hk0 | exact Hv0 ] ].
Qed.

Lemma outcome_dom_exact_add {p} (r : Index.Snapshot.NodeRef p) (occ : Index.Occurrence)
    (rest : list (Index.Snapshot.NodeRef p * Index.Occurrence)) m_rest (v : ExpressionOutcome p) e
    (Hv : Index.view_expr occ = Some e) :
  outcome_dom_exact rest m_rest ->
  outcome_dom_exact ((r, occ) :: rest) (Index.KeyMap.add (Index.Snapshot.node_ref_key r) v m_rest).
Proof.
  intros Hdom k Hk.
  assert (HIn : Index.KeyMap.In k
                  (Index.KeyMap.add (Index.Snapshot.node_ref_key r) v m_rest))
    by (rewrite Index.KeyFacts.in_find_iff; exact Hk).
  apply Index.KeyFacts.add_in_iff in HIn. destruct HIn as [Heq | HIn0].
  - exists r, occ, e. split; [left; reflexivity | split; [ exact Heq | exact Hv ] ].
  - assert (Hkm : Index.KeyMap.find k m_rest <> None)
      by (rewrite <- Index.KeyFacts.in_find_iff; exact HIn0).
    destruct (Hdom k Hkm) as [r0 [occ0 [e0 [Hin0 [Hk0 Hv0]]]]].
    exists r0, occ0, e0. split; [right; exact Hin0 | split; [ exact Hk0 | exact Hv0 ] ].
Qed.

(* the resolved target is read from the passed-in table object, never recomputed *)
Lemma conv_target_table_type {p} (idx : Index.Snapshot.Syntax p) (tnft : TypeNameFacts p)
    (er : Index.ExprRef p) ts x Hv :
  fact_type (type_name_fact_at_table tnft (conversion_target_ref_tot idx er ts x Hv))
  = predeclared_type ts.
Proof.
  destruct (conversion_target_ref_of_view idx er ts x Hv) as [tr0 [Hc [_ [_ Hsyn]]]].
  rewrite (conversion_target_ref_tot_eq idx er ts x Hv tr0 Hc).
  rewrite (type_name_fact_at_table_resolves tnft tr0 ts Hsyn). reflexivity.
Qed.

(* a leaf's stored outcome is its own constant analysis, with no fallback value *)
Lemma leaf_stored_matches {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p)
    (er : Index.ExprRef p) occ e (ci : Typing.ConstantInfo)
    (Hv : Index.view_expr occ = Some e)
    (Hrole : Index.occurrence_role occ = expression_ref_role er)
    (Hci : constant_info e = Some ci) :
  outcome_matches idx r occ (leaf_outcome er ci).
Proof.
  cbn [outcome_matches leaf_outcome].
  rewrite (occurrence_expr_fact_status occ e ci Hv Hci).
  do 2 f_equal. rewrite <- Hrole. symmetry.
  exact (use_resolved_of_input_eq occ e ci Hv Hci).
Qed.

(* a conversion's stored outcome matches: one conversion call, or a genuine local failure *)
Lemma conv_stored_matches {p} (idx : Index.Snapshot.Syntax p) (tnft : TypeNameFacts p)
    (r : Index.Snapshot.NodeRef p) (er opr : Index.ExprRef p) (tr : Index.TypeNameRef p) occ operand_occ ts x
    (Hae : Index.as_expr idx r = Some er)
    (Hv : Index.view_expr occ = Some (Syntax.Convert ts x))
    (Hrole : Index.occurrence_role occ = expression_ref_role er)
    (Htr : fact_type (type_name_fact_at_table tnft tr) = predeclared_type ts)
    (Htr_ref : conversion_target_ref idx er = Some tr)
    (Hopr_ref : conversion_operand_ref idx er = Some opr)
    (operand_out : ExpressionOutcome p)
    (Hout_proj : outcome_proj_fact operand_out operand_occ)
    (Hopr_view : Index.view_expr operand_occ = Some x) :
  outcome_matches idx r occ (conv_outcome tnft er tr opr operand_out).
Proof.
  unfold conv_outcome. destruct operand_out as [opf|c1 c2 c3 c4 c5| ].
  - (* operand succeeded: opf carries [constant_info x] *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occurrence_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (constant_info x) as [cx|] eqn:Ecx; [| discriminate Hout_proj].
    injection Hout_proj as Hopf. subst opf. cbn [const_status].
    rewrite Htr.
    destruct (Typing.convert_constant (predeclared_type ts) cx) as [tc|] eqn:Ecv.
    + (* conversion succeeds: ExpressionSuccess typed fact = occurrence's [constant_info] *)
      assert (Hci : constant_info (Syntax.Convert ts x) = Some (Typing.TypedInfo (predeclared_type ts) tc)).
      { rewrite const_info_conv_eq, Ecx. cbn [option_map]. rewrite Ecv. reflexivity. }
      cbn [outcome_matches].
      rewrite (occurrence_expr_fact_status occ (Syntax.Convert ts x) (Typing.TypedInfo (predeclared_type ts) tc) Hv Hci).
      do 2 f_equal. rewrite <- Hrole. symmetry.
      exact (use_resolved_of_input_eq occ (Syntax.Convert ts x) (Typing.TypedInfo (predeclared_type ts) tc) Hv Hci).
    + (* conversion rejects: ConversionFailure carrying a genuine [local_conv_failure] + retained refs *)
      assert (Hlcf : local_conv_failure (Syntax.Convert ts x) = Some (predeclared_type ts, cx))
        by (cbn [local_conv_failure]; rewrite Ecx, Ecv; reflexivity).
      cbn [outcome_matches]. split.
      * unfold occurrence_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. cbn [option_map]. rewrite Ecv. reflexivity.
      * unfold outcome_convfail_ev.
        split; [ exact Hae
               | split; [ exists (Syntax.Convert ts x); split; [exact Hv | exact Hlcf]
                        | split; [ exact Htr_ref | exact Hopr_ref ] ] ].
  - (* operand was a local invalid conversion: no operand fact => blocked, no fact + no local failure here *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occurrence_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (constant_info x) as [cx|] eqn:Ecx; [discriminate Hout_proj|].
    cbn [outcome_matches]. split.
    + unfold occurrence_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. reflexivity.
    + exists (Syntax.Convert ts x). split; [exact Hv | cbn [local_conv_failure]; rewrite Ecx; reflexivity].
  - (* operand was blocked-by-child: same *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occurrence_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (constant_info x) as [cx|] eqn:Ecx; [discriminate Hout_proj|].
    cbn [outcome_matches]. split.
    + unfold occurrence_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. reflexivity.
    + exists (Syntax.Convert ts x). split; [exact Hv | cbn [local_conv_failure]; rewrite Ecx; reflexivity].
Qed.

(* a visited expression's reference as data, minted totally rather than skipped when absent *)
Lemma program_visit_as_expr_not_none {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p) occ e :
  In (r, occ) (program_visit p) -> Index.view_expr occ = Some e -> Index.as_expr idx r <> None.
Proof. intros Hin Hv. destruct (program_visit_as_expr p idx r occ e Hin Hv) as [er [Hae _]]. rewrite Hae. discriminate. Qed.
Definition program_visit_expr_ref {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p) occ e
    (Hin : In (r, occ) (program_visit p)) (Hv : Index.view_expr occ = Some e)
  : { er : Index.ExprRef p | Index.as_expr idx r = Some er /\ Index.erase_ref er = r }.
Proof.
  destruct (Index.as_expr idx r) as [er|] eqn:E.
  - exists er. split; [reflexivity | exact (Index.erase_as_kind idx r Index.ExpressionKind er E)].
  - exfalso. exact (program_visit_as_expr_not_none idx r occ e Hin Hv E).
Defined.

(* every expression reference views an expression, so the total queries need no option *)
Definition expression_ref_view_opt {p} (er : Index.ExprRef p) : option Syntax.Expr :=
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)).
Lemma expression_ref_view_not_none {p} (er : Index.ExprRef p) : expression_ref_view_opt er <> None.
Proof.
  unfold expression_ref_view_opt.
  destruct (Index.kind_view_expr _ (Index.noderefof_kind er)) as [e Hv]. rewrite Hv. discriminate.
Qed.
Definition expression_ref_view {p} (er : Index.ExprRef p) : Syntax.Expr :=
  from_some (expression_ref_view_opt er) (expression_ref_view_not_none er).
Lemma expression_ref_view_eq {p} (er : Index.ExprRef p) :
  Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some (expression_ref_view er).
Proof.
  destruct (Index.kind_view_expr _ (Index.noderefof_kind er)) as [e Hv].
  assert (E : expression_ref_view_opt er = Some e) by exact Hv.
  unfold expression_ref_view. rewrite (from_some_eq _ (expression_ref_view_not_none er) e E). exact Hv.
Qed.

(** the type-name table built from the exact retained visit, which transports its exactness *)
Lemma type_name_input_map_eq {p} (input : Input p) :
  fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) (input_visit input) = program_type_name_facts p.
Proof. unfold program_type_name_facts. rewrite (input_visit_ok input). reflexivity. Qed.

Definition build_type_name_fact_table {p} (input : Input p) : TypeNameFacts p.
Proof.
  refine (MakeTypeNameFacts
            (fold_right add_tn_fact (Index.KeyMap.empty TypeNameFact) (input_visit input)) _ _).
  - intros k f Hf. rewrite (type_name_input_map_eq input) in Hf. exact (program_type_name_facts_domain p k f Hf).
  - intros r occ Hin. rewrite (type_name_input_map_eq input). exact (program_type_name_facts_find p r occ Hin).
Defined.

(* the retained-input table is the canonical one, and its total query resolves the source name *)
Lemma build_type_name_map {p} (input : Input p) :
  type_name_map (build_type_name_fact_table input) = program_type_name_facts p.
Proof. exact (type_name_input_map_eq input). Qed.

(** minting a visited expression's reference is total, so no occurrence is skipped *)
Lemma fold_ext_in {A B} (f g : A -> B -> B) (init : B) (l : list A) :
  (forall a b, In a l -> f a b = g a b) -> fold_right f init l = fold_right g init l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [fold_right]. rewrite IH by (intros a' b Ha'; apply H; right; exact Ha').
  apply H; left; reflexivity.
Qed.
Lemma fold_right_map {A B C} (f : B -> C -> C) (g : A -> B) (init : C) (l : list A) :
  fold_right f init (map g l) = fold_right (fun x => f (g x)) init l.
Proof. induction l as [|a l IH]; [reflexivity | cbn [map fold_right]; rewrite IH; reflexivity]. Qed.

(** each conversion work item carries its own target and operand references and their index facts *)
Definition ConvRefinement {p} (input : Input p) (er : Index.ExprRef p) (e : Syntax.Expr) : Type :=
  match e with
  | Syntax.Convert ts x =>
      { tr : Index.TypeNameRef p & { opr : Index.ExprRef p |
          conversion_target_ref (index input) er = Some tr
          /\ Index.type_name_ref_syntax tr = Some ts
          /\ conversion_operand_ref (index input) er = Some opr } }
  | _ => unit
  end.

(** one proof-backed work item per live expression occurrence, carrying its refs and its refinement *)
Record Work {p} (input : Input p) : Type := MakeWork {
  work_node_ref   : Index.Snapshot.NodeRef p ;
  work_occurrence : Index.Occurrence ;
  work_expr_ref   : Index.ExprRef p ;
  work_expr       : Syntax.Expr ;
  work_in_visit      : In (work_node_ref, work_occurrence) (input_visit input) ;
  work_view_exact    : Index.view_expr work_occurrence = Some work_expr ;
  work_as_expr_exact : Index.as_expr (index input) work_node_ref = Some work_expr_ref ;
  work_erase_exact   : Index.erase_ref work_expr_ref = work_node_ref ;
  work_conv          : ConvRefinement input work_expr_ref work_expr
}.
Arguments MakeWork {p input} _ _ _ _ _ _ _ _ _.
Arguments work_node_ref {p input} _.  Arguments work_occurrence {p input} _.
Arguments work_expr_ref {p input} _.  Arguments work_expr {p input} _.
Arguments work_in_visit {p input} _.  Arguments work_view_exact {p input} _.
Arguments work_as_expr_exact {p input} _.  Arguments work_erase_exact {p input} _.
Arguments work_conv {p input} _.

(* whole-visit membership transports to [program_visit] membership through the retained coherence [input_visit_ok]. *)
Definition in_program {p} {input : Input p} {ro} (H : In ro (input_visit input)) : In ro (program_visit p) :=
  eq_ind (input_visit input) (fun L => In ro L) H (program_visit p) (input_visit_ok input).

(* the refinement is built once from the occurrence's own proofs, so the refs are computed in one place *)
Definition build_work_conversion {p} (input : Input p) (nr : Index.Snapshot.NodeRef p)
    (occ : Index.Occurrence) (er : Index.ExprRef p) (e : Syntax.Expr)
    (Hin : In (nr, occ) (input_visit input)) (Hview : Index.view_expr occ = Some e)
    (Hae : Index.as_expr (index input) nr = Some er) : ConvRefinement input er e.
Proof.
  destruct e as [ b|nn|n0|s|dd|dc| ts x ]; try exact tt.
  (* the refs are data, so the impossible cases and the source recovery both discharge in Prop *)
  destruct (conversion_target_ref (index input) er) as [tr|] eqn:Htr;
    [ | exfalso; destruct (conversion_target_ref_conv (index input) nr occ er ts x (in_program Hin) Hview Hae)
          as [tr0 [Htr0 _]]; rewrite Htr in Htr0; discriminate Htr0 ].
  destruct (conversion_operand_ref (index input) er) as [opr|] eqn:Hopr;
    [ | exfalso; destruct (conversion_operand_ref_conv (index input) nr occ er ts x (in_program Hin) Hview Hae)
          as [opr0 [Hopr0 _]]; rewrite Hopr in Hopr0; discriminate Hopr0 ].
  assert (Htsyn : Index.type_name_ref_syntax tr = Some ts).
  { destruct (conversion_target_ref_conv (index input) nr occ er ts x (in_program Hin) Hview Hae)
      as [tr0 [Htr0 [_ [_ Hts0]]]].
    rewrite Htr in Htr0. injection Htr0 as Htreq. subst tr0. exact Hts0. }
  exact (existT _ tr (exist _ opr (conj Htr (conj Htsyn Hopr)))).
Defined.

(** the outcome table's domain is exactly the work key set, so a table with an extra key is uninhabitable *)
Definition occurrence_is_expr {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence) : bool :=
  match Index.view_expr (snd ro) with Some _ => true | None => false end.
Lemma occurrence_is_expr_true {p} (r : Index.Snapshot.NodeRef p) occ e :
  Index.view_expr occ = Some e -> occurrence_is_expr (r, occ) = true.
Proof. intro H. unfold occurrence_is_expr. cbn [snd]. rewrite H. reflexivity. Qed.
Lemma occurrence_is_expr_false {p} (r : Index.Snapshot.NodeRef p) occ :
  Index.view_expr occ = None -> occurrence_is_expr (r, occ) = false.
Proof. intro H. unfold occurrence_is_expr. cbn [snd]. rewrite H. reflexivity. Qed.

Definition build_forest_sig {p} (input : Input p) :
  forall (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)),
    (forall ro, In ro l -> In ro (input_visit input)) ->
    { items : list (Work input) |
        map (fun w => (work_node_ref w, work_occurrence w)) items = filter occurrence_is_expr l }.
Proof.
  induction l as [| [r occ] rest IH]; intro Hsub.
  - exists nil. reflexivity.
  - assert (Hin : In (r, occ) (input_visit input)) by (apply Hsub; left; reflexivity).
    destruct (IH (fun ro Hro => Hsub ro (or_intror Hro))) as [items_rest Hrest].
    destruct (Index.view_expr occ) as [e|] eqn:Hv.
    + assert (Hinp : In (r, occ) (program_visit p)) by (rewrite <- (input_visit_ok input); exact Hin).
      destruct (program_visit_expr_ref (index input) r occ e Hinp Hv) as [er [Hae Her]].
      exists (MakeWork r occ er e Hin Hv Hae Her (build_work_conversion input r occ er e Hin Hv Hae) :: items_rest).
      cbn [map filter work_node_ref work_occurrence]. rewrite (occurrence_is_expr_true r occ e Hv), Hrest. reflexivity.
    + exists items_rest.
      cbn [filter]. rewrite (occurrence_is_expr_false r occ Hv). exact Hrest.
Defined.

Lemma map_concat_eq {A B} (f : A -> B) (ls : list (list A)) :
  map f (concat ls) = concat (map (map f) ls).
Proof. induction ls as [|a ls IH]; [reflexivity | cbn [concat map]; rewrite map_app, IH; reflexivity]. Qed.
Lemma filter_concat_eq {A} (g : A -> bool) (ls : list (list A)) :
  filter g (concat ls) = concat (map (filter g) ls).
Proof. induction ls as [|a ls IH]; [reflexivity | cbn [concat map]; rewrite filter_app, IH; reflexivity]. Qed.

(* whole-program block membership: every occurrence of a block is in the retained visit. *)
Definition input_visit_of_concat {p} (input : Input p) ro
    (H : In ro (concat (input_blocks input))) : In ro (input_visit input) :=
  eq_ind_r (fun L => In ro L) H (input_visit_blocks input).

(* the PER-BLOCK forest (§4 [forest_blocks]): the exact expression-work items of each retained block, built ONCE. *)
Definition build_forest_blocks {p} (input : Input p) :
  forall (blocks : list (list (Index.Snapshot.NodeRef p * Index.Occurrence))),
    (forall ro, In ro (concat blocks) -> In ro (input_visit input)) ->
    { bs : list (list (Work input)) |
        map (map (fun w => (work_node_ref w, work_occurrence w))) bs = map (filter occurrence_is_expr) blocks }.
Proof.
  induction blocks as [| blk rest IH]; intro Hsub.
  - exists nil. reflexivity.
  - destruct (build_forest_sig input blk
                (fun ro H => Hsub ro (in_or_app blk (concat rest) ro (or_introl H)))) as [items Hitems].
    destruct (IH (fun ro H => Hsub ro (in_or_app blk (concat rest) ro (or_intror H)))) as [bsrest Hrest].
    exists (items :: bsrest). cbn [map]. rewrite Hitems, Hrest. reflexivity.
Defined.

(* filtering preserves the NoDup of a projection [map g]. *)
Lemma nodup_map_filter {A B} (g : A -> B) (f : A -> bool) (L : list A) :
  NoDup (map g L) -> NoDup (map g (filter f L)).
Proof.
  induction L as [|a L IH]; [cbn; intro; constructor|].
  cbn [map]. intro H. apply NoDup_cons_iff in H. destruct H as [Hni Hnd].
  cbn [filter]. destruct (f a) eqn:Ef.
  - cbn [map]. apply NoDup_cons_iff. split; [| exact (IH Hnd)].
    intro Hin. apply Hni. apply in_map_iff in Hin. destruct Hin as [a' [Hg Ha']].
    apply filter_In in Ha'. apply in_map_iff. exists a'. split; [exact Hg | exact (proj1 Ha')].
  - exact (IH Hnd).
Qed.

(** the retained list is the source-order authority; identity is a derived index over the standard map *)
Fixpoint work_index_map {p} {input : Input p} (items : list (Work input))
  : Index.KeyMap.t (Work input) :=
  match items with
  | nil => Index.KeyMap.empty (Work input)
  | w :: rest =>
      Index.KeyMap.add (Index.Snapshot.node_ref_key (work_node_ref w)) w (work_index_map rest)
  end.

(* every add writes a key the partial map does not hold, so the build never silently overwrites *)
Lemma work_index_fresh {p} {input : Input p} (items : list (Work input)) k :
  ~ In k (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) items) ->
  Index.KeyMap.find k (work_index_map items) = None.
Proof.
  induction items as [|w rest IH]; cbn [work_index_map map]; intro Hni.
  - apply Index.KeyFacts.empty_o.
  - assert (Hne : Index.Snapshot.node_ref_key (work_node_ref w) <> k)
      by (intro Heq; apply Hni; left; exact Heq).
    rewrite (Index.key_map_add_unequal _ _ _ _ Hne).
    apply IH. intro H. apply Hni. right. exact H.
Qed.

(* the per-step freshness the fold actually relies on, stated at the [cons] the builder takes. *)
Lemma work_index_add_fresh {p} {input : Input p} (w : Work input) (rest : list (Work input)) :
  NoDup (map (fun w0 => Index.Snapshot.node_ref_key (work_node_ref w0)) (w :: rest)) ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w)) (work_index_map rest) = None.
Proof.
  cbn [map]. intro Hnd. apply NoDup_cons_iff in Hnd. exact (work_index_fresh rest _ (proj1 Hnd)).
Qed.

(* the finished map finds exactly the retained item with that key, soundly and completely *)
Lemma work_index_exact {p} {input : Input p} (items : list (Work input)) :
  NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) items) ->
  forall k w,
    Index.KeyMap.find k (work_index_map items) = Some w
    <-> (In w items /\ Index.Snapshot.node_ref_key (work_node_ref w) = k).
Proof.
  induction items as [|w0 rest IH]; cbn [work_index_map map]; intro Hnd; intros k w.
  - rewrite Index.KeyFacts.empty_o. split; [discriminate | intros [[] _]].
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd].
    destruct (Index.key_eq_dec (Index.Snapshot.node_ref_key (work_node_ref w0)) k) as [Heq|Hne].
    + rewrite <- Heq, Index.key_map_add_equal. split.
      * intro H. injection H as Hw. subst w. split; [left; reflexivity | reflexivity].
      * intros [Hin Hk]. destruct Hin as [Hw0 | Hin]; [rewrite Hw0; reflexivity |].
        exfalso. apply Hni. rewrite <- Hk.
        exact (in_map (fun w1 => Index.Snapshot.node_ref_key (work_node_ref w1)) rest w Hin).
    + rewrite (Index.key_map_add_unequal _ _ _ _ Hne). rewrite (IH Hnd k w). split.
      * intros [Hin Hk]. split; [right; exact Hin | exact Hk].
      * intros [Hin Hk]. destruct Hin as [Hw0 | Hin];
          [exfalso; apply Hne; rewrite Hw0; exact Hk | split; [exact Hin | exact Hk]].
Qed.

(** the index object: the standard map plus its bidirectional law, indexed by the list it indexes *)
Record WorkIndex {p} {input : Input p} (items : list (Work input)) : Type :=
  MakeWorkIndex {
    index_map   : Index.KeyMap.t (Work input) ;
    index_exact : forall k w,
      Index.KeyMap.find k index_map = Some w
      <-> (In w items /\ Index.Snapshot.node_ref_key (work_node_ref w) = k)
  }.
Arguments MakeWorkIndex {p input items} _ _.
Arguments index_map {p input items} _.  Arguments index_exact {p input items} _.

(* the builder is total precisely because duplicate-freedom is a proof argument, not a checked hope *)
Definition build_work_index {p} {input : Input p} (items : list (Work input))
    (Hnd : NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) items)) : WorkIndex items :=
  MakeWorkIndex (work_index_map items) (work_index_exact items Hnd).

(* DERIVED domain: the index holds exactly the retained items' keys. *)
Lemma index_domain {p} {input : Input p} {items : list (Work input)}
    (idx : WorkIndex items) (k : Index.Key) :
  Index.KeyMap.find k (index_map idx) <> None
  <-> exists w, In w items /\ Index.Snapshot.node_ref_key (work_node_ref w) = k.
Proof.
  split.
  - intro Hne. destruct (Index.KeyMap.find k (index_map idx)) as [w|] eqn:Eo;
      [| exfalso; exact (Hne eq_refl)].
    exists w. exact (proj1 (index_exact idx k w) Eo).
  - intros [w [Hin Hk]].
    rewrite (proj2 (index_exact idx k w) (conj Hin Hk)). discriminate.
Qed.

(* two retained items with equal keys are the same item, straight from the standard map *)
Lemma index_key_inj {p} {input : Input p} {items : list (Work input)}
    (idx : WorkIndex items) (a b : Work input) :
  In a items -> In b items ->
  Index.Snapshot.node_ref_key (work_node_ref a) = Index.Snapshot.node_ref_key (work_node_ref b) -> a = b.
Proof.
  intros Ha Hb Hk.
  pose proof (proj2 (index_exact idx (Index.Snapshot.node_ref_key (work_node_ref a)) a) (conj Ha eq_refl)) as Hfa.
  pose proof (proj2 (index_exact idx (Index.Snapshot.node_ref_key (work_node_ref a)) b) (conj Hb (eq_sym Hk))) as Hfb.
  rewrite Hfa in Hfb. injection Hfb as H. exact H.
Qed.

(* the total member query is one standard find, whose impossible branch is discharged in Prop *)
Definition index_member_at {p} {input : Input p} {items : list (Work input)}
    (idx : WorkIndex items) (k : Index.Key)
    (Hex : exists w, In w items /\ Index.Snapshot.node_ref_key (work_node_ref w) = k)
  : { w : Work input | In w items /\ Index.Snapshot.node_ref_key (work_node_ref w) = k }.
Proof.
  destruct (Index.KeyMap.find k (index_map idx)) as [w0|] eqn:Eo.
  - exists w0. exact (proj1 (index_exact idx k w0) Eo).
  - exfalso. destruct Hex as [w [Hin Hkey]].
    rewrite (proj2 (index_exact idx k w) (conj Hin Hkey)) in Eo. discriminate Eo.
Defined.

(* at a retained member's own key the query returns that very member *)
Lemma index_member_at_retained {p} {input : Input p} {items : list (Work input)}
    (idx : WorkIndex items) (w : Work input) (Hin : In w items) Hex :
  proj1_sig (index_member_at idx (Index.Snapshot.node_ref_key (work_node_ref w)) Hex) = w.
Proof.
  destruct (index_member_at idx (Index.Snapshot.node_ref_key (work_node_ref w)) Hex) as [w' [Hin' Hk']].
  cbn [proj1_sig]. exact (index_key_inj idx w' w Hin' Hin Hk').
Qed.

(* a key held by NO retained item has no index entry: a foreign key is absent, never answered with a stand-in. *)
Lemma index_no_foreign {p} {input : Input p} {items : list (Work input)}
    (idx : WorkIndex items) (k : Index.Key) :
  (forall w, In w items -> Index.Snapshot.node_ref_key (work_node_ref w) <> k) ->
  Index.KeyMap.find k (index_map idx) = None.
Proof.
  intro Hno. destruct (Index.KeyMap.find k (index_map idx)) as [w|] eqn:Eo; [| reflexivity].
  exfalso. destruct (proj1 (index_exact idx k w) Eo) as [Hin Hk]. exact (Hno w Hin Hk).
Qed.

(** the one work forest object, retaining its blocks, its flat item list and both projection proofs *)
Record WorkForest {p} (input : Input p) : Type := MakeForest {
  forest_blocks : list (list (Work input)) ;
  forest_items  : list (Work input) ;
  forest_flat   : forest_items = concat forest_blocks ;
  forest_blocks_exact :
    map (map (fun w => (work_node_ref w, work_occurrence w))) forest_blocks
    = map (filter occurrence_is_expr) (input_blocks input) ;
  forest_items_exact :
    map (fun w => (work_node_ref w, work_occurrence w)) forest_items
    = filter occurrence_is_expr (input_visit input) ;
  forest_keys_nodup :
    NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) forest_items) ;
  forest_index : WorkIndex forest_items ;
  forest_reverse :
    forall w, In w forest_items -> In (work_node_ref w, work_occurrence w) (input_visit input) ;
  forest_forward :
    forall nr occ e, In (nr, occ) (input_visit input) -> Index.view_expr occ = Some e ->
      exists w, In w forest_items /\ work_node_ref w = nr /\ work_occurrence w = occ
}.
Arguments MakeForest {p input} _ _ _ _ _ _ _ _ _.
Arguments forest_blocks {p input} _.  Arguments forest_items {p input} _.  Arguments forest_flat {p input} _.
Arguments forest_blocks_exact {p input} _.  Arguments forest_items_exact {p input} _.
Arguments forest_keys_nodup {p input} _.  Arguments forest_index {p input} _.
Arguments forest_reverse {p input} _.  Arguments forest_forward {p input} _.

(* the sole work-discovery call, whose proof is stored into the forest rather than discarded *)
Definition build_expr_work_forest {p} (input : Input p) : WorkForest input.
Proof.
  destruct (build_forest_blocks input (input_blocks input) (input_visit_of_concat input)) as [bs Hbs].
  assert (Hitems : map (fun w => (work_node_ref w, work_occurrence w)) (concat bs)
                   = filter occurrence_is_expr (input_visit input)).
  { rewrite map_concat_eq, Hbs, <- filter_concat_eq, <- (input_visit_blocks input). reflexivity. }
  assert (Hnd : NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) (concat bs))).
  { replace (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) (concat bs))
      with (map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (filter occurrence_is_expr (input_visit input)))
      by (rewrite <- Hitems, map_map; reflexivity).
    apply nodup_map_filter. rewrite (input_visit_ok input). exact (program_visit_key_nodup p). }
  (* the ONE index build, over the item list ALREADY built above — no second discovery, no re-traversal. *)
  refine (MakeForest bs (concat bs) eq_refl Hbs Hitems Hnd (build_work_index (concat bs) Hnd) _ _).
  - (* forest_reverse *)
    intros w Hw. pose proof (in_map (fun w0 => (work_node_ref w0, work_occurrence w0)) _ _ Hw) as Hp.
    rewrite Hitems in Hp. apply filter_In in Hp. exact (proj1 Hp).
  - (* forest_forward *)
    intros nr occ e Hin Hv.
    assert (Hf : In (nr, occ) (filter occurrence_is_expr (input_visit input))).
    { apply filter_In. split; [exact Hin | unfold occurrence_is_expr; cbn [snd]; rewrite Hv; reflexivity]. }
    rewrite <- Hitems in Hf. apply in_map_iff in Hf. destruct Hf as [w [Hpair Hinw]].
    injection Hpair as Hnr Hocc. exists w. split; [exact Hinw | split; [exact Hnr | exact Hocc]].
Defined.

(* the retained item pairs are duplicate-free, derived from the stored projection rather than rebuilt *)
Lemma forest_pairs_nodup {p} {input : Input p} (forest : WorkForest input) :
  NoDup (map (fun w => (work_node_ref w, work_occurrence w)) (forest_items forest)).
Proof.
  rewrite (forest_items_exact forest). apply NoDup_filter.
  apply (NoDup_map_inv (fun ro => Index.Snapshot.node_ref_key (fst ro))).
  rewrite (input_visit_ok input). exact (program_visit_key_nodup p).
Qed.

(* splitting the forest at a member induces the matching visit split, derived from the stored fields *)
Lemma forest_split {p} {input : Input p} (forest : WorkForest input)
    ipre (w : Work input) irest :
  forest_items forest = ipre ++ w :: irest ->
  exists vpre vrest,
    input_visit input = vpre ++ (work_node_ref w, work_occurrence w) :: vrest
    /\ map (fun w0 => (work_node_ref w0, work_occurrence w0)) irest = filter occurrence_is_expr vrest.
Proof.
  intro Hsplit.
  assert (Hwp : In (work_node_ref w, work_occurrence w) (filter occurrence_is_expr (input_visit input))).
  { rewrite <- (forest_items_exact forest), Hsplit, map_app. cbn [map]. apply in_or_app; right; left; reflexivity. }
  destruct (proj1 (filter_In _ _ _) Hwp) as [Hwin _].
  apply in_split in Hwin. destruct Hwin as [vpre [vrest Hvsplit]].
  exists vpre, vrest. split; [exact Hvsplit |].
  assert (Hfil : filter occurrence_is_expr (input_visit input)
                 = filter occurrence_is_expr vpre ++ (work_node_ref w, work_occurrence w) :: filter occurrence_is_expr vrest).
  { rewrite Hvsplit, filter_app. cbn [filter].
    rewrite (occurrence_is_expr_true (work_node_ref w) (work_occurrence w) (work_expr w) (work_view_exact w)). reflexivity. }
  assert (Hfor : filter occurrence_is_expr (input_visit input)
                 = map (fun w0 => (work_node_ref w0, work_occurrence w0)) ipre
                   ++ (work_node_ref w, work_occurrence w) :: map (fun w0 => (work_node_ref w0, work_occurrence w0)) irest).
  { rewrite <- (forest_items_exact forest), Hsplit, map_app. cbn [map]. reflexivity. }
  pose proof (forest_pairs_nodup forest) as Hnd1. rewrite Hsplit, map_app in Hnd1. cbn [map] in Hnd1.
  pose proof (forest_pairs_nodup forest) as Hnd2. rewrite (forest_items_exact forest), Hfil in Hnd2.
  apply (split_unique (work_node_ref w, work_occurrence w)
           (map (fun w0 => (work_node_ref w0, work_occurrence w0)) ipre)
           (map (fun w0 => (work_node_ref w0, work_occurrence w0)) irest)
           (filter occurrence_is_expr vpre) (filter occurrence_is_expr vrest)).
  - rewrite <- Hfor. exact Hfil.
  - intro Hbad. apply (NoDup_remove_2 _ _ _ Hnd1). apply in_or_app; left; exact Hbad.
  - intro Hbad. apply (NoDup_remove_2 _ _ _ Hnd2). apply in_or_app; left; exact Hbad.
Qed.

(* a conversion member's operand lies in the processed suffix of the retained forest *)
Lemma forest_operand_in_tail {p} {input : Input p} (forest : WorkForest input)
    ipre (w : Work input) irest ts x :
  forest_items forest = ipre ++ w :: irest ->
  Index.view_expr (work_occurrence w) = Some (Syntax.Convert ts x) ->
  exists w', In w' irest /\ Index.Snapshot.node_ref_key (work_node_ref w') = operand_key (work_node_ref w).
Proof.
  intros Hsplit Hwv.
  destruct (forest_split forest ipre w irest Hsplit) as [vpre [vrest [Hvsplit Hirest_eq]]].
  assert (Hpv : program_visit p = vpre ++ (work_node_ref w, work_occurrence w) :: vrest)
    by (rewrite <- (input_visit_ok input); exact Hvsplit).
  destruct (program_visit_operand_closed p (index input) vpre (work_node_ref w) (work_occurrence w) vrest Hpv
              (Syntax.Convert ts x) x Hwv eq_refl) as [r' [occ' [Hkey' [Hvx' Hin']]]].
  assert (Hinf : In (r', occ') (filter occurrence_is_expr vrest)).
  { apply filter_In. split; [exact Hin' | exact (occurrence_is_expr_true r' occ' x Hvx')]. }
  rewrite <- Hirest_eq in Hinf. apply in_map_iff in Hinf. destruct Hinf as [w' [Hpair Hinw']].
  injection Hpair as Hnr' Hocc'. exists w'. split; [exact Hinw' | rewrite Hnr'; exact Hkey'].
Qed.

(** a work member is a retained handle, recovered by one standard find rather than by a keyed scan *)
Definition WorkMember {p} {input : Input p} (forest : WorkForest input) : Type :=
  { w : Work input | In w (forest_items forest) }.

(* the retained member is recovered through the forest's own index; the ordered list is not consulted *)
Definition forest_index_member_at {p} {input : Input p} (forest : WorkForest input)
    (k : Index.Key)
    (Hex : exists w, In w (forest_items forest) /\ Index.Snapshot.node_ref_key (work_node_ref w) = k)
  : { w : Work input | In w (forest_items forest) /\ Index.Snapshot.node_ref_key (work_node_ref w) = k } :=
  index_member_at (forest_index forest) k Hex.

(* the forest-level query returns the very retained member asked about. *)
Lemma forest_index_member_at_retained {p} {input : Input p} (forest : WorkForest input)
    (w : Work input) (Hin : In w (forest_items forest)) Hex :
  proj1_sig (forest_index_member_at forest (Index.Snapshot.node_ref_key (work_node_ref w)) Hex) = w.
Proof. exact (index_member_at_retained (forest_index forest) w Hin Hex). Qed.

(* a key held by no retained member is absent from the forest's index — no foreign key is ever answered. *)
Lemma forest_index_no_foreign {p} {input : Input p} (forest : WorkForest input)
    (k : Index.Key) :
  (forall w, In w (forest_items forest) -> Index.Snapshot.node_ref_key (work_node_ref w) <> k) ->
  Index.KeyMap.find k (index_map (forest_index forest)) = None.
Proof. exact (index_no_foreign (forest_index forest) k). Qed.

(* a visited occurrence that is not an expression has no index entry *)
Lemma index_nonexpr_absent {p} {input : Input p} (forest : WorkForest input)
    (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (input_visit input) -> Index.view_expr occ = None ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r) (index_map (forest_index forest)) = None.
Proof.
  intros Hin Hv. apply forest_index_no_foreign. intros w Hinw Hk.
  assert (Hrr : work_node_ref w = r) by (apply Index.Snapshot.node_ref_key_inj; exact Hk).
  assert (Hoc : work_occurrence w = occ).
  { rewrite (program_visit_occ_is_source p (work_node_ref w) (work_occurrence w) (in_program (work_in_visit w))).
    rewrite Hrr, (program_visit_occ_is_source p r occ (in_program Hin)). reflexivity. }
  pose proof (work_view_exact w) as Hve. rewrite Hoc, Hv in Hve. discriminate Hve.
Qed.

Record Conversion {p} {input : Input p} (forest : WorkForest input)
    (w : Work input) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Type := MakeConversion {
  conversion_target_node_ref   : Index.TypeNameRef p ;
  conversion_operand_work : WorkMember forest ;
  conversion_target_ref_eq  : conversion_target_ref (index input) (work_expr_ref w) = Some conversion_target_node_ref ;
  conversion_operand_ref_eq : conversion_operand_ref (index input) (work_expr_ref w)
                      = Some (work_expr_ref (proj1_sig conversion_operand_work)) ;
  conversion_target_syntax  : Index.type_name_ref_syntax conversion_target_node_ref = Some ts ;
  conversion_target_role    : Index.occurrence_role
                        (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref conversion_target_node_ref))
                      = Index.ConversionTarget ;
  conversion_operand_role   : Index.occurrence_role (work_occurrence (proj1_sig conversion_operand_work))
                      = Index.ConversionOperand ;
  conversion_operand_expr   : work_expr (proj1_sig conversion_operand_work) = x ;
  conversion_target_key     : Index.Snapshot.node_ref_key (Index.erase_ref conversion_target_node_ref) = type_name_key (work_node_ref w) ;
  conversion_operand_key    : Index.Snapshot.node_ref_key (work_node_ref (proj1_sig conversion_operand_work))
                      = operand_key (work_node_ref w) ;
  conversion_target_before_op : Pos.lt (Index.key_local (type_name_key (work_node_ref w)))
                               (Index.key_local (operand_key (work_node_ref w)))
}.
Arguments MakeConversion {p input forest w ts x} _ _ _ _ _ _ _ _ _ _ _.
Arguments conversion_target_node_ref {p input forest w ts x} _.  Arguments conversion_operand_work {p input forest w ts x} _.
Arguments conversion_target_ref_eq {p input forest w ts x} _.  Arguments conversion_operand_ref_eq {p input forest w ts x} _.
Arguments conversion_target_syntax {p input forest w ts x} _.  Arguments conversion_target_role {p input forest w ts x} _.
Arguments conversion_operand_role {p input forest w ts x} _.  Arguments conversion_operand_expr {p input forest w ts x} _.
Arguments conversion_target_key {p input forest w ts x} _.  Arguments conversion_operand_key {p input forest w ts x} _.
Arguments conversion_target_before_op {p input forest w ts x} _.

Definition build_conversion_work {p} {input : Input p} (forest : WorkForest input)
    (w : Work input) ts x (Hview : Index.view_expr (work_occurrence w) = Some (Syntax.Convert ts x))
  : Conversion forest w ts x.
Proof.
  (* [work_expr w = Syntax.Convert ts x], so [work_conv w] is the conversion refinement carrying [tr]/[opr] as DATA. *)
  assert (Hew : work_expr w = Syntax.Convert ts x)
    by (pose proof (work_view_exact w) as Hv; rewrite Hview in Hv; injection Hv as He; exact (eq_sym He)).
  pose proof (work_conv w) as Hcv. rewrite Hew in Hcv. cbn [ConvRefinement] in Hcv.
  destruct Hcv as [tr [opr [Htr_ref [Htsyn Hopr_ref]]]].
  (* the operand ref's occurrence facts (roles/keys/view = x) are recovered in Prop, never eliminated into Type. *)
  assert (Haexp : Index.as_expr (index input) (work_node_ref w) = Some (work_expr_ref w)) by exact (work_as_expr_exact w).
  assert (Hinp : In (work_node_ref w, work_occurrence w) (program_visit p)) by exact (in_program (work_in_visit w)).
  assert (Hopr_key : Index.Snapshot.node_ref_key (Index.erase_ref opr) = operand_key (work_node_ref w)).
  { destruct (conversion_operand_ref_conv (index input) (work_node_ref w) (work_occurrence w) (work_expr_ref w) ts x
                Hinp Hview Haexp) as [opr0 [Hopr0 [Hk0 _]]].
    rewrite Hopr_ref in Hopr0. injection Hopr0 as Ho; subst opr0. exact Hk0. }
  assert (Hopr_view : Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) = Some x).
  { destruct (conversion_operand_ref_conv (index input) (work_node_ref w) (work_occurrence w) (work_expr_ref w) ts x
                Hinp Hview Haexp) as [opr0 [Hopr0 [_ [_ Hview0]]]].
    rewrite Hopr_ref in Hopr0. injection Hopr0 as Ho; subst opr0. exact Hview0. }
  assert (Hopr_role : Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr))
                      = Index.ConversionOperand).
  { destruct (conversion_operand_ref_conv (index input) (work_node_ref w) (work_occurrence w) (work_expr_ref w) ts x
                Hinp Hview Haexp) as [opr0 [Hopr0 [_ [Hrole0 _]]]].
    rewrite Hopr_ref in Hopr0. injection Hopr0 as Ho; subst opr0. exact Hrole0. }
  assert (Htr_key : Index.Snapshot.node_ref_key (Index.erase_ref tr) = type_name_key (work_node_ref w)).
  { destruct (conversion_target_ref_conv (index input) (work_node_ref w) (work_occurrence w) (work_expr_ref w) ts x
                Hinp Hview Haexp) as [tr0 [Htr0 [Hk0 _]]].
    rewrite Htr_ref in Htr0. injection Htr0 as Ht; subst tr0. exact Hk0. }
  assert (Htr_role : Index.occurrence_role (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr))
                     = Index.ConversionTarget).
  { destruct (conversion_target_ref_conv (index input) (work_node_ref w) (work_occurrence w) (work_expr_ref w) ts x
                Hinp Hview Haexp) as [tr0 [Htr0 [_ [Hrole0 _]]]].
    rewrite Htr_ref in Htr0. injection Htr0 as Ht; subst tr0. exact Hrole0. }
  (* the operand member is recovered at the key the work item already carries, never at a guessed one *)
  assert (Hopr_in : In (Index.erase_ref opr,
                        Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) (input_visit input))
    by (rewrite (input_visit_ok input); exact (noderef_in_prog_visit p (Index.erase_ref opr))).
  assert (Hex : exists w', In w' (forest_items forest)
                  /\ Index.Snapshot.node_ref_key (work_node_ref w')
                     = Index.Snapshot.node_ref_key (Index.erase_ref opr)).
  { destruct (forest_forward forest (Index.erase_ref opr)
                (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)) x Hopr_in Hopr_view)
      as [w' [Hinw' [Hnr' _]]].
    exists w'. split; [exact Hinw' | rewrite Hnr'; reflexivity]. }
  destruct (forest_index_member_at forest (Index.Snapshot.node_ref_key (Index.erase_ref opr)) Hex)
    as [wopr [Hwopr_in Hwopr_ref_key]].
  assert (Hnode : work_node_ref wopr = Index.erase_ref opr)
    by (apply Index.Snapshot.node_ref_key_inj; exact Hwopr_ref_key).
  assert (Hwopr_key : Index.Snapshot.node_ref_key (work_node_ref wopr) = operand_key (work_node_ref w))
    by (rewrite Hwopr_ref_key; exact Hopr_key).
  assert (Hocc : work_occurrence wopr = Index.Snapshot.source_occurrence_of_ref (Index.erase_ref opr)).
  { rewrite (program_visit_occ_is_source p (work_node_ref wopr) (work_occurrence wopr) (in_program (work_in_visit wopr))).
    rewrite Hnode. reflexivity. }
  assert (Href : work_expr_ref wopr = opr).
  { pose proof (work_as_expr_exact wopr) as Hae2. rewrite Hnode in Hae2.
    rewrite (as_expr_erase (index input) opr) in Hae2. injection Hae2 as He2. exact (eq_sym He2). }
  assert (Hexpr : work_expr wopr = x).
  { pose proof (work_view_exact wopr) as Hv2. rewrite Hocc, Hopr_view in Hv2. injection Hv2 as Hx. exact (eq_sym Hx). }
  refine (MakeConversion tr (exist _ wopr Hwopr_in) Htr_ref _ Htsyn Htr_role _ Hexpr Htr_key Hwopr_key _).
  - cbn [proj1_sig]. rewrite Href. exact Hopr_ref.
  - cbn [proj1_sig]. rewrite Hocc. exact Hopr_role.
  - unfold type_name_key, operand_key. cbn [Index.key_local]. apply Pos.lt_succ_diag_r.
Defined.

(* two retained members with the same key are equal, read off the standard map rather than a scan *)
Lemma forest_key_inj {p} {input : Input p} (forest : WorkForest input) (a b : Work input) :
  In a (forest_items forest) -> In b (forest_items forest) ->
  Index.Snapshot.node_ref_key (work_node_ref a) = Index.Snapshot.node_ref_key (work_node_ref b) -> a = b.
Proof. exact (index_key_inj (forest_index forest) a b). Qed.

(* a suffix member is a retained member proved to lie in the exact list the accumulator processes *)
Definition SuffixMember {p} {input : Input p} (forest : WorkForest input)
    (items : list (Work input)) : Type :=
  { wm : WorkMember forest | In (proj1_sig wm) items }.
Definition sm_work {p} {input : Input p} {forest : WorkForest input} {items}
    (sm : SuffixMember forest items) : Work input := proj1_sig (proj1_sig sm).
Definition sm_key {p} {input : Input p} {forest : WorkForest input} {items}
    (sm : SuffixMember forest items) : Index.Key :=
  Index.Snapshot.node_ref_key (work_node_ref (sm_work sm)).

(* a conversion step: the current member, its conversion view, and its operand as a suffix member *)
Record ConversionStep {p} {input : Input p} (forest : WorkForest input)
    (current : Work input) (rest : list (Work input)) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Type :=
  MakeConversionStep {
    step_current        : WorkMember forest ;
    step_current_exact  : proj1_sig step_current = current ;
    step_conversion     : Conversion forest current ts x ;
    step_operand_suffix : SuffixMember forest rest ;
    step_operand_exact  : proj1_sig (proj1_sig step_operand_suffix) = proj1_sig (conversion_operand_work step_conversion)
  }.
Arguments MakeConversionStep {p input forest current rest ts x} _ _ _ _ _.
Arguments step_current {p input forest current rest ts x} _.
Arguments step_current_exact {p input forest current rest ts x} _.
Arguments step_conversion {p input forest current rest ts x} _.
Arguments step_operand_suffix {p input forest current rest ts x} _.
Arguments step_operand_exact {p input forest current rest ts x} _.

(* the operand member comes from the work item itself, so no raw operand key lives in this step *)
Definition build_conversion_step {p} {input : Input p} (forest : WorkForest input)
    (w : Work input) (rest : list (Work input)) ts x
    (Hin_w : In w (forest_items forest))
    (Hsplit : exists ipre, forest_items forest = ipre ++ w :: rest)
    (Hview : Index.view_expr (work_occurrence w) = Some (Syntax.Convert ts x))
  : ConversionStep forest w rest ts x.
Proof.
  pose (cwk := build_conversion_work forest w ts x Hview).
  (* the operand member is already in Type, so the Prop reasoning stays inside its own assertion *)
  assert (Hopin_rest : In (proj1_sig (conversion_operand_work cwk)) rest).
  { destruct Hsplit as [ipre Hpre].
    destruct (forest_operand_in_tail forest ipre w rest ts x Hpre Hview) as [w' [Hinw' Hkeyw']].
    assert (Hopin : In (proj1_sig (conversion_operand_work cwk)) (forest_items forest))
      by exact (proj2_sig (conversion_operand_work cwk)).
    assert (Hw'_in : In w' (forest_items forest))
      by (rewrite Hpre; apply in_or_app; right; right; exact Hinw').
    assert (Hsame : proj1_sig (conversion_operand_work cwk) = w').
    { apply (forest_key_inj forest _ _ Hopin Hw'_in).
      rewrite (conversion_operand_key cwk), Hkeyw'. reflexivity. }
    rewrite Hsame. exact Hinw'. }
  exact (MakeConversionStep (exist _ w Hin_w) eq_refl cwk (exist _ (conversion_operand_work cwk) Hopin_rest) eq_refl).
Defined.

(* the accumulator carries its coverage, so a missing outcome is unrepresentable rather than optional *)
Record Accumulator {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) (items : list (Work input)) : Type :=
  MakeAccumulator {
    accumulator_map    : Index.KeyMap.t (ExpressionOutcome p) ;
    accumulator_covers : forall w, In w items ->
                  Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w)) accumulator_map <> None ;
    accumulator_domain : outcome_dom_exact (map (fun w0 => (work_node_ref w0, work_occurrence w0)) items) accumulator_map
  }.
Arguments MakeAccumulator {p input forest tnft items} _ _ _.
Arguments accumulator_map {p input forest tnft items} _.
Arguments accumulator_covers {p input forest tnft items} _.
Arguments accumulator_domain {p input forest tnft items} _.

(* the total suffix-member query, which the fold uses instead of a raw find *)
Definition accumulator_total {p} {input : Input p} {forest : WorkForest input} {tnft} {items}
    (acc : Accumulator forest tnft items) (sm : SuffixMember forest items) : ExpressionOutcome p :=
  from_some (Index.KeyMap.find (sm_key sm) (accumulator_map acc))
            (accumulator_covers acc (sm_work sm) (proj2_sig sm)).

(* the direct cause reads its operand's outcome through the exact suffix member, then converts once *)
Inductive StepCause {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) (current : Work input) (rest : list (Work input))
    (acc_rest : Accumulator forest tnft rest) : ExpressionOutcome p -> Prop :=
| LeafCause : forall ci,
    Typing.expression_child (work_expr current) = None -> constant_info (work_expr current) = Some ci ->
    StepCause forest tnft current rest acc_rest (leaf_outcome (work_expr_ref current) ci)
| ConversionSuccessCause : forall ts x (step : ConversionStep forest current rest ts x) opf tc,
    proj1_sig (step_current step) = current ->
    work_expr current = Syntax.Convert ts x ->
    accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf ->
    Typing.convert_constant (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))))
      (const_status opf) = Some tc ->
    StepCause forest tnft current rest acc_rest
      (ExpressionSuccess (MakeExpressionFact
               (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))) tc)
               (use_resolved_of_input (expression_ref_role (work_expr_ref current))
                  (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))) tc))))
| ConversionFailureCause : forall ts x (step : ConversionStep forest current rest ts x) opf,
    proj1_sig (step_current step) = current ->
    work_expr current = Syntax.Convert ts x ->
    accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf ->
    Typing.convert_constant (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))))
      (const_status opf) = None ->
    StepCause forest tnft current rest acc_rest
      (ConversionFailure (work_expr_ref current) (conversion_target_node_ref (step_conversion step))
         (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
         (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))) (const_status opf))
| ChildFailureCause : forall ts x (step : ConversionStep forest current rest ts x),
    proj1_sig (step_current step) = current ->
    work_expr current = Syntax.Convert ts x ->
    outcome_is_fail (accumulator_total acc_rest (step_operand_suffix step)) ->
    StepCause forest tnft current rest acc_rest ChildFailure.
Arguments LeafCause {p input forest tnft current rest acc_rest} _ _ _.
Arguments ConversionSuccessCause {p input forest tnft current rest acc_rest} _ _ _ _ _ _ _ _ _.
Arguments ConversionFailureCause {p input forest tnft current rest acc_rest} _ _ _ _ _ _ _ _.
Arguments ChildFailureCause {p input forest tnft current rest acc_rest} _ _ _ _ _ _.

(* a retained member's occurrence role IS its ExprRef's role (both read the member's own source occurrence). *)
Lemma work_occ_role {p} {input : Input p} (w : Work input) :
  Index.occurrence_role (work_occurrence w) = expression_ref_role (work_expr_ref w).
Proof.
  unfold expression_ref_role. rewrite (work_erase_exact w),
    (program_visit_occ_is_source p (work_node_ref w) (work_occurrence w) (in_program (work_in_visit w))). reflexivity.
Qed.

(* a conversion step's outcome matches the specification, given that its operand's does *)
Lemma conv_step_matches {p} {input : Input p} {forest : WorkForest input} {tnft}
    (current : Work input) (rest : list (Work input))
    (acc_rest : Accumulator forest tnft rest) ts x (step : ConversionStep forest current rest ts x)
    (He : work_expr current = Syntax.Convert ts x)
    (Hops : forall sm_op : SuffixMember forest rest,
       outcome_matches (index input) (work_node_ref (sm_work sm_op)) (work_occurrence (sm_work sm_op))
         (accumulator_total acc_rest sm_op)) :
  outcome_matches (index input) (work_node_ref current) (work_occurrence current)
    (conv_outcome tnft (work_expr_ref current) (conversion_target_node_ref (step_conversion step))
       (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
       (accumulator_total acc_rest (step_operand_suffix step))).
Proof.
  pose proof (Hops (step_operand_suffix step)) as Hopm.
  unfold sm_work in Hopm. rewrite (step_operand_exact step) in Hopm.
  assert (Hoprv : Index.view_expr (work_occurrence (proj1_sig (conversion_operand_work (step_conversion step)))) = Some x)
    by (rewrite (work_view_exact (proj1_sig (conversion_operand_work (step_conversion step)))),
          (conversion_operand_expr (step_conversion step)); reflexivity).
  assert (Htnf : fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))) = predeclared_type ts)
    by (rewrite (type_name_fact_at_table_resolves tnft (conversion_target_node_ref (step_conversion step)) ts
                   (conversion_target_syntax (step_conversion step))); reflexivity).
  exact (conv_stored_matches (index input) tnft (work_node_ref current) (work_expr_ref current)
           (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step)))) (conversion_target_node_ref (step_conversion step))
           (work_occurrence current) (work_occurrence (proj1_sig (conversion_operand_work (step_conversion step)))) ts x
           (work_as_expr_exact current)
           (ltac:(rewrite (work_view_exact current), He; reflexivity))
           (work_occ_role current) Htnf
           (conversion_target_ref_eq (step_conversion step)) (conversion_operand_ref_eq (step_conversion step))
           (accumulator_total acc_rest (step_operand_suffix step))
           (outcome_matches_proj (index input) (work_node_ref (proj1_sig (conversion_operand_work (step_conversion step))))
              (work_occurrence (proj1_sig (conversion_operand_work (step_conversion step))))
              (accumulator_total acc_rest (step_operand_suffix step)) Hopm)
           Hoprv).
Qed.

(** the separate specification bridge, supplied by the fold's own recursion rather than by production *)
Lemma stepcause_matches {p} {input : Input p} {forest : WorkForest input} {tnft}
    (current : Work input) (rest : list (Work input))
    (acc_rest : Accumulator forest tnft rest) o :
  StepCause forest tnft current rest acc_rest o ->
  (forall sm_op : SuffixMember forest rest,
     outcome_matches (index input) (work_node_ref (sm_work sm_op)) (work_occurrence (sm_work sm_op))
       (accumulator_total acc_rest sm_op)) ->
  outcome_matches (index input) (work_node_ref current) (work_occurrence current) o.
Proof.
  intros Hsc Hops. destruct Hsc as [ ci Hnone Hconst
                                   | ts x step opf tc Hcur He Hop Hconv
                                   | ts x step opf Hcur He Hop Hconv
                                   | ts x step Hcur He Hfail ].
  - exact (leaf_stored_matches (index input) (work_node_ref current) (work_expr_ref current)
             (work_occurrence current) (work_expr current) ci (work_view_exact current)
             (work_occ_role current) Hconst).
  - (* the success cause equals the conversion outcome over a succeeding operand *)
    enough (Hm : outcome_matches (index input) (work_node_ref current) (work_occurrence current)
                   (conv_outcome tnft (work_expr_ref current) (conversion_target_node_ref (step_conversion step))
                      (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                      (accumulator_total acc_rest (step_operand_suffix step)))).
    { revert Hm. rewrite Hop. cbn [conv_outcome]. rewrite Hconv. exact (fun H => H). }
    apply conv_step_matches; assumption.
  - (* ConversionFailureCause *)
    enough (Hm : outcome_matches (index input) (work_node_ref current) (work_occurrence current)
                   (conv_outcome tnft (work_expr_ref current) (conversion_target_node_ref (step_conversion step))
                      (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                      (accumulator_total acc_rest (step_operand_suffix step)))).
    { revert Hm. rewrite Hop. cbn [conv_outcome]. rewrite Hconv. exact (fun H => H). }
    apply conv_step_matches; assumption.
  - (* ChildFailureCause: operand failed, so [conv_outcome] is [ChildFailure] *)
    enough (Hm : outcome_matches (index input) (work_node_ref current) (work_occurrence current)
                   (conv_outcome tnft (work_expr_ref current) (conversion_target_node_ref (step_conversion step))
                      (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                      (accumulator_total acc_rest (step_operand_suffix step)))).
    { revert Hm. unfold conv_outcome.
      destruct (accumulator_total acc_rest (step_operand_suffix step)) as [opf| | ];
        [ cbn [outcome_is_fail] in Hfail; destruct Hfail | exact (fun H => H) | exact (fun H => H) ]. }
    apply conv_step_matches; assumption.
Qed.

(* the extension primitive and the causal trace: one accumulator step, retaining each cons node's cause *)
Definition empty_acc {p} {input : Input p} {forest : WorkForest input} {tnft}
  : Accumulator forest tnft [].
Proof.
  refine (MakeAccumulator (items := @nil (Work input))
            (Index.KeyMap.empty (ExpressionOutcome p)) _ outcome_dom_exact_empty).
  intros w0 Hin0. destruct Hin0.
Defined.

(* an add never removes a key, so coverage extends without needing freshness *)
Lemma extend_covers {p} {input : Input p} {forest : WorkForest input} {tnft}
    {rest : list (Work input)} (acc_rest : Accumulator forest tnft rest)
    (current : Work input) (o : ExpressionOutcome p) :
  forall w, In w (current :: rest) ->
    Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w))
      (Index.KeyMap.add (Index.Snapshot.node_ref_key (work_node_ref current)) o (accumulator_map acc_rest)) <> None.
Proof.
  intros w0 Hin0.
  destruct (Index.key_eq_dec (Index.Snapshot.node_ref_key (work_node_ref w0))
              (Index.Snapshot.node_ref_key (work_node_ref current))) as [Heq|Hne].
  - rewrite Heq, Index.key_map_add_equal. discriminate.
  - rewrite Index.key_map_add_unequal by (intro Hbad; apply Hne; symmetry; exact Hbad).
    destruct Hin0 as [Hcur | Hin0].
    + exfalso. apply Hne. rewrite Hcur. reflexivity.
    + exact (accumulator_covers acc_rest w0 Hin0).
Qed.

(* the exact domain of the extended map (via [outcome_dom_exact_add] with the head's own [work_view_exact]). *)
Lemma extend_domain {p} {input : Input p} {forest : WorkForest input} {tnft}
    {rest : list (Work input)} (acc_rest : Accumulator forest tnft rest)
    (current : Work input) (o : ExpressionOutcome p) :
  outcome_dom_exact (map (fun w0 => (work_node_ref w0, work_occurrence w0)) (current :: rest))
    (Index.KeyMap.add (Index.Snapshot.node_ref_key (work_node_ref current)) o (accumulator_map acc_rest)).
Proof.
  cbn [map]. eapply outcome_dom_exact_add; [ exact (work_view_exact current) | exact (accumulator_domain acc_rest) ].
Qed.

(* the SINGLE accumulator step: extend [acc_rest] with the head [current]'s outcome [o] at [current]'s own key. *)
Definition extend_acc {p} {input : Input p} {forest : WorkForest input} {tnft}
    {rest : list (Work input)} (acc_rest : Accumulator forest tnft rest)
    (current : Work input) (o : ExpressionOutcome p)
  : Accumulator forest tnft (current :: rest) :=
  MakeAccumulator
    (Index.KeyMap.add (Index.Snapshot.node_ref_key (work_node_ref current)) o (accumulator_map acc_rest))
    (extend_covers acc_rest current o)
    (extend_domain acc_rest current o).

(* lift a [SuffixMember] of [rest] to a [SuffixMember] of [current :: rest] (the SAME retained member). *)
Definition sm_lift_cons {p} {input : Input p} {forest : WorkForest input}
    {rest : list (Work input)} (current : Work input) (sm : SuffixMember forest rest)
  : SuffixMember forest (current :: rest) :=
  exist _ (proj1_sig sm) (or_intror (proj2_sig sm)).

(* the query depends only on the member's key, so one member has one outcome however membership was proved *)
Lemma accumulator_total_irrel {p} {input : Input p} {forest : WorkForest input} {tnft}
    {items : list (Work input)} (acc : Accumulator forest tnft items)
    (wm : WorkMember forest) (H1 H2 : In (proj1_sig wm) items) :
  accumulator_total acc (exist _ wm H1) = accumulator_total acc (exist _ wm H2).
Proof. unfold accumulator_total. apply from_some_pi. Qed.

(* the HEAD query: at a member whose key IS the extended head's key, the extended accumulator returns exactly [o]. *)
Lemma extend_here_query {p} {input : Input p} {forest : WorkForest input} {tnft}
    {rest : list (Work input)} (acc_rest : Accumulator forest tnft rest)
    (current : Work input) (o : ExpressionOutcome p) (sm : SuffixMember forest (current :: rest)) :
  sm_key sm = Index.Snapshot.node_ref_key (work_node_ref current) ->
  accumulator_total (extend_acc acc_rest current o) sm = o.
Proof.
  intro Hk. unfold accumulator_total. apply from_some_eq.
  unfold extend_acc; cbn [accumulator_map]. rewrite Hk. apply Index.key_map_add_equal.
Qed.

(* the TAIL query PRESERVATION (one step): extending by a FRESH head leaves every tail member's outcome unchanged. *)
Lemma extend_tail_query {p} {input : Input p} {forest : WorkForest input} {tnft}
    {rest : list (Work input)} (acc_rest : Accumulator forest tnft rest)
    (current : Work input) (o : ExpressionOutcome p)
    (Hfresh : ~ In (Index.Snapshot.node_ref_key (work_node_ref current))
                   (map (fun w0 => Index.Snapshot.node_ref_key (work_node_ref w0)) rest))
    (sm : SuffixMember forest rest) :
  accumulator_total (extend_acc acc_rest current o) (sm_lift_cons current sm) = accumulator_total acc_rest sm.
Proof.
  assert (Hne : sm_key sm <> Index.Snapshot.node_ref_key (work_node_ref current)).
  { intro Hbad. apply Hfresh. rewrite <- Hbad. apply in_map_iff.
    exists (sm_work sm). split; [reflexivity | exact (proj2_sig sm)]. }
  unfold accumulator_total at 1. apply from_some_eq.
  unfold extend_acc; cbn [accumulator_map].
  rewrite Index.key_map_add_unequal by (intro Hbad; apply Hne; symmetry; exact Hbad).
  exact (from_some_some (Index.KeyMap.find (sm_key sm) (accumulator_map acc_rest))
           (accumulator_covers acc_rest (sm_work sm) (proj2_sig sm))).
Qed.

(* the causal trace, indexed by the accumulator it builds and retaining each step's exact cause *)
Inductive Trace {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p)
  : forall (items : list (Work input)), Accumulator forest tnft items -> Type :=
| EmptyTrace : Trace forest tnft [] empty_acc
| TraceStep : forall (current : Work input) (rest : list (Work input))
                (acc_rest : Accumulator forest tnft rest) (o : ExpressionOutcome p),
              In current (forest_items forest) ->
              ~ In (Index.Snapshot.node_ref_key (work_node_ref current))
                   (map (fun w0 => Index.Snapshot.node_ref_key (work_node_ref w0)) rest) ->
              Trace forest tnft rest acc_rest ->
              StepCause forest tnft current rest acc_rest o ->
              Trace forest tnft (current :: rest) (extend_acc acc_rest current o).
Arguments EmptyTrace {p input forest tnft}.
Arguments TraceStep {p input forest tnft} _ _ _ _ _ _ _ _.

(* a member's retained cause: its suffix split, its prior accumulator, and the tail-to-final closure *)
Definition RetainedMemberCause {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) (items : list (Work input))
    (acc : Accumulator forest tnft items) (sm : SuffixMember forest items) : Type :=
  { rest : list (Work input) &
  { acc_rest : Accumulator forest tnft rest &
    ( ( (exists prefix, items = prefix ++ sm_work sm :: rest)
        * StepCause forest tnft (sm_work sm) rest acc_rest (accumulator_total acc sm) )
      * (forall (sm2 : SuffixMember forest rest) (Hlift : In (sm_work sm2) items),
           accumulator_total acc_rest sm2 = accumulator_total acc (exist _ (proj1_sig sm2) Hlift)) )%type } }.

(* each member's insertion cause and its query preservation, projected by induction on the trace *)
Lemma trace_retained_cause {p} {input : Input p} {forest : WorkForest input} {tnft} :
  forall items acc (t : Trace forest tnft items acc) (sm : SuffixMember forest items),
    RetainedMemberCause forest tnft items acc sm.
Proof.
  intros items acc t.
  induction t as [ | current rest acc_rest o Hin_c Hfresh tail IH sc ]; intro sm.
  - destruct (proj2_sig sm).
  - destruct (Index.key_eq_dec (sm_key sm) (Index.Snapshot.node_ref_key (work_node_ref current)))
      as [Hhead | Htail].
    + (* HEAD: this member IS [current] *)
      assert (Hsw : sm_work sm = current)
        by (apply (forest_key_inj forest (sm_work sm) current (proj2_sig (proj1_sig sm)) Hin_c); exact Hhead).
      assert (Ho : accumulator_total (extend_acc acc_rest current o) sm = o)
        by (apply extend_here_query; exact Hhead).
      exists rest, acc_rest. split; [ split | ].
      * exists (@nil (Work input)). cbn [app]. rewrite Hsw. reflexivity.
      * rewrite Ho, Hsw. exact sc.
      * intros sm2 Hlift.
        rewrite (accumulator_total_irrel (extend_acc acc_rest current o) (proj1_sig sm2) Hlift
                   (or_intror (proj2_sig sm2))).
        symmetry. exact (extend_tail_query acc_rest current o Hfresh sm2).
    + (* TAIL: this member is in [rest] *)
      assert (Hin_rest : In (sm_work sm) rest).
      { destruct (proj2_sig sm) as [Hcur | Hin].
        - exfalso. apply Htail. unfold sm_key. do 2 f_equal. exact (eq_sym Hcur).
        - exact Hin. }
      pose (sm' := exist (fun wm => In (proj1_sig wm) rest) (proj1_sig sm) Hin_rest
             : SuffixMember forest rest).
      destruct (IH sm') as [rest_w [acc_rest_w [[Hsplit_w sc_w] Hpreserve_w]]].
      assert (Hq : accumulator_total (extend_acc acc_rest current o) sm = accumulator_total acc_rest sm').
      { rewrite <- (extend_tail_query acc_rest current o Hfresh sm'). apply accumulator_total_irrel. }
      exists rest_w, acc_rest_w. split; [ split | ].
      * destruct Hsplit_w as [prefix_w Hpre_w].
        exists (current :: prefix_w). cbn [app]. f_equal. exact Hpre_w.
      * rewrite Hq. exact sc_w.
      * intros sm2 Hlift2.
        assert (Hlift_rest : In (sm_work sm2) rest).
        { destruct Hsplit_w as [prefix_w Hpre_w]. rewrite Hpre_w.
          apply in_or_app. right. right. exact (proj2_sig sm2). }
        transitivity (accumulator_total acc_rest
                        (exist (fun wm => In (proj1_sig wm) rest) (proj1_sig sm2) Hlift_rest)).
        -- exact (Hpreserve_w sm2 Hlift_rest).
        -- transitivity (accumulator_total (extend_acc acc_rest current o)
                           (sm_lift_cons current
                              (exist (fun wm => In (proj1_sig wm) rest) (proj1_sig sm2) Hlift_rest))).
           ++ symmetry. exact (extend_tail_query acc_rest current o Hfresh
                                 (exist (fun wm => In (proj1_sig wm) rest) (proj1_sig sm2) Hlift_rest)).
           ++ apply accumulator_total_irrel.
Qed.

(* the source-specification match for every retained member, a separate bridge from the causal evidence *)
Lemma trace_match {p} {input : Input p} {forest : WorkForest input} {tnft} :
  forall items acc (t : Trace forest tnft items acc) (sm : SuffixMember forest items),
    outcome_matches (index input) (work_node_ref (sm_work sm)) (work_occurrence (sm_work sm)) (accumulator_total acc sm).
Proof.
  intros items acc t.
  induction t as [ | current rest acc_rest o Hin_c Hfresh tail IH sc ]; intro sm.
  - destruct (proj2_sig sm).
  - destruct (Index.key_eq_dec (sm_key sm) (Index.Snapshot.node_ref_key (work_node_ref current)))
      as [Hhead | Htail].
    + assert (Hsw : sm_work sm = current)
        by (apply (forest_key_inj forest (sm_work sm) current (proj2_sig (proj1_sig sm)) Hin_c); exact Hhead).
      assert (Ho : accumulator_total (extend_acc acc_rest current o) sm = o)
        by (apply extend_here_query; exact Hhead).
      rewrite Ho, Hsw. exact (stepcause_matches current rest acc_rest o sc IH).
    + assert (Hin_rest : In (sm_work sm) rest).
      { destruct (proj2_sig sm) as [Hcur | Hin].
        - exfalso. apply Htail. unfold sm_key. do 2 f_equal. exact (eq_sym Hcur).
        - exact Hin. }
      pose (sm' := exist (fun wm => In (proj1_sig wm) rest) (proj1_sig sm) Hin_rest
             : SuffixMember forest rest).
      assert (Hq : accumulator_total (extend_acc acc_rest current o) sm = accumulator_total acc_rest sm')
        by (rewrite <- (extend_tail_query acc_rest current o Hfresh sm'); apply accumulator_total_irrel).
      rewrite Hq. exact (IH sm').
Qed.

(* the fold builds the one causal object, each conversion reading its operand through the exact member *)
Definition build_outcome_trace {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) :
  forall (items : list (Work input)),
    (exists ipre, forest_items forest = ipre ++ items) ->
    { acc : Accumulator forest tnft items & Trace forest tnft items acc }.
Proof.
  induction items as [| w rest IH]; intro Hsuf.
  - exists empty_acc. exact EmptyTrace.
  - assert (Hsuf_rest : exists ipre, forest_items forest = ipre ++ rest).
    { destruct Hsuf as [ipre Hpre]. exists (ipre ++ [w]). rewrite <- app_assoc. exact Hpre. }
    destruct (IH Hsuf_rest) as [acc_rest tail].
    assert (Hin_w : In w (forest_items forest)).
    { destruct Hsuf as [ipre Hpre]. rewrite Hpre. apply in_or_app; right; left; reflexivity. }
    assert (Hnd : ~ In (Index.Snapshot.node_ref_key (work_node_ref w))
                    (map (fun w0 => Index.Snapshot.node_ref_key (work_node_ref w0)) rest)).
    { destruct Hsuf as [ipre Hpre]. pose proof (forest_keys_nodup forest) as Hnd0.
      rewrite Hpre, map_app in Hnd0. cbn [map] in Hnd0. apply NoDup_remove_2 in Hnd0.
      intro Hbad. apply Hnd0. apply in_or_app; right; exact Hbad. }
    pose proof (work_view_exact w) as Hvx.
    assert (Hstep : { o : ExpressionOutcome p & StepCause forest tnft w rest acc_rest o }).
    { destruct (work_expr w) as [b|nn|n0|s|dd|dc|ts x] eqn:He.
      1-6: (assert (Hleaf : Typing.expression_child (work_expr w) = None) by (rewrite He; reflexivity);
            eexists; exact (LeafCause (leaf_const (work_expr w) Hleaf) Hleaf (leaf_const_status (work_expr w) Hleaf))).
      assert (Hview : Index.view_expr (work_occurrence w) = Some (Syntax.Convert ts x))
        by (rewrite (work_view_exact w), He; reflexivity).
      pose (step := build_conversion_step forest w rest ts x Hin_w Hsuf Hview).
      destruct (accumulator_total acc_rest (step_operand_suffix step)) as [opf|er2 tr2 opr2 t2 ci2|] eqn:Hop.
      + destruct (Typing.convert_constant
                    (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))))
                    (const_status opf)) as [tc|] eqn:Hconv.
        * eexists. exact (ConversionSuccessCause ts x step opf tc (step_current_exact step) He Hop Hconv).
        * eexists. exact (ConversionFailureCause ts x step opf (step_current_exact step) He Hop Hconv).
      + eexists. refine (ChildFailureCause ts x step (step_current_exact step) He _). rewrite Hop; exact I.
      + eexists. refine (ChildFailureCause ts x step (step_current_exact step) He _). rewrite Hop; exact I. }
    destruct Hstep as [o sc].
    exists (extend_acc acc_rest w o).
    exact (TraceStep w rest acc_rest o Hin_w Hnd tail sc).
Defined.


(** the forest-indexed outcome table: the map paired with its direct cause and its exact domain *)
Definition wm_suffix {p} {input : Input p} {forest : WorkForest input} (wm : WorkMember forest)
  : SuffixMember forest (forest_items forest) := exist _ wm (proj2_sig wm).

(* the outcome table is the causal object: the accumulator paired with the trace that built it *)
Record Outcomes {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) : Type :=
  MakeOutcomes {
    outcomes_acc : Accumulator forest tnft (forest_items forest) ;
    outcomes_trace : Trace forest tnft (forest_items forest) outcomes_acc
  }.
Arguments MakeOutcomes {p input forest tnft} _ _.
Arguments outcomes_acc {p input forest tnft} _.  Arguments outcomes_trace {p input forest tnft} _.

(* the map and exact domain, projected from the retained accumulator *)
Definition outcomes_map {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) : Index.KeyMap.t (ExpressionOutcome p) := accumulator_map (outcomes_acc ot).
Definition outcomes_dom {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) :
    outcome_dom_exact (map (fun w0 => (work_node_ref w0, work_occurrence w0)) (forest_items forest)) (outcomes_map ot) :=
  accumulator_domain (outcomes_acc ot).

Definition build_forest_outcome_table {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) : Outcomes forest tnft :=
  let bt := build_outcome_trace forest tnft (forest_items forest)
              (ex_intro _ (@nil (Work input)) eq_refl) in
  MakeOutcomes (projT1 bt) (projT2 bt).

(* a retained member's key is present, from its membership rather than from an equal-key search *)
Definition outcomes_present {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (w : Work input) (Hin : In w (forest_items forest))
  : Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w)) (outcomes_map ot) <> None :=
  accumulator_covers (outcomes_acc ot) w Hin.

(* the total outcome query consumes a retained member, never a raw option or a constructible work item *)
Definition total_forest_outcome_at {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) : ExpressionOutcome p :=
  from_some (Index.KeyMap.find
               (Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))) (outcomes_map ot))
            (outcomes_present ot (proj1_sig wm) (proj2_sig wm)).

(* a key is in the table exactly when a retained forest item has it *)
Lemma outcomes_domain_iff_forest {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) k :
  Index.KeyMap.find k (outcomes_map ot) <> None
  <-> exists w, In w (forest_items forest) /\ Index.Snapshot.node_ref_key (work_node_ref w) = k.
Proof.
  split.
  - intro Hk. destruct (outcomes_dom ot k Hk) as [r [occ [e [Hin [Hkey Hv]]]]].
    apply in_map_iff in Hin. destruct Hin as [w [Hpair Hinw]].
    injection Hpair as Hnr Hocc. exists w. split; [exact Hinw | rewrite Hnr; exact Hkey].
  - intros [w [Hinw Hkey]]. rewrite <- Hkey. exact (outcomes_present ot w Hinw).
Qed.

(* a visited non-expression occurrence has no entry, so it is never mistaken for expression work *)
Lemma outcomes_nonexpr_absent {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (input_visit input) -> Index.view_expr occ = None ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r) (outcomes_map ot) = None.
Proof.
  intros Hin Hv.
  destruct (Index.KeyMap.find (Index.Snapshot.node_ref_key r) (outcomes_map ot)) as [w|] eqn:E;
    [exfalso | reflexivity].
  destruct (outcomes_dom ot (Index.Snapshot.node_ref_key r) (ltac:(rewrite E; discriminate)))
    as [r' [occ' [e' [Hin' [Hk' Hv']]]]].
  apply in_map_iff in Hin'. destruct Hin' as [w0 [Hpair Hinw0]].
  injection Hpair as Hnr Hocc. subst r' occ'.
  assert (Hrr : work_node_ref w0 = r) by (apply Index.Snapshot.node_ref_key_inj; exact Hk').
  assert (Hoc : work_occurrence w0 = occ).
  { rewrite (program_visit_occ_is_source p (work_node_ref w0) (work_occurrence w0) (in_program (work_in_visit w0))).
    rewrite Hrr, (program_visit_occ_is_source p r occ (in_program Hin)). reflexivity. }
  rewrite Hoc, Hv in Hv'. discriminate Hv'.
Qed.

(* a per-element step that is a no-op on the filtered-OUT elements folds the same over [l] and [filter f l]. *)
Lemma fold_right_filter_skip {A B} (fo : A -> B -> B) (f : A -> bool) (init : B) (l : list A) :
  (forall a b, In a l -> f a = false -> fo a b = b) ->
  fold_right fo init l = fold_right fo init (filter f l).
Proof.
  induction l as [|a l IH]; intro Hskip; [reflexivity|].
  cbn [filter]. destruct (f a) eqn:Ef.
  - cbn [fold_right]. rewrite (IH (fun a' b Ha' => Hskip a' b (or_intror Ha'))). reflexivity.
  - cbn [fold_right]. rewrite (Hskip a (fold_right fo init l) (or_introl eq_refl) Ef).
    exact (IH (fun a' b Ha' => Hskip a' b (or_intror Ha'))).
Qed.

Lemma occurrence_is_expr_false_view {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence) :
  occurrence_is_expr ro = false -> Index.view_expr (snd ro) = None.
Proof. unfold occurrence_is_expr. destruct (Index.view_expr (snd ro)); [discriminate | reflexivity]. Qed.

(** a per-work fold equals a per-occurrence fold when they agree on work and the latter skips the rest *)
Lemma forest_fold {p} {input : Input p} (forest : WorkForest input) {B}
    (fw : Work input -> B -> B)
    (fo : (Index.Snapshot.NodeRef p * Index.Occurrence) -> B -> B) (init : B)
    (Hagree : forall w b, fw w b = fo (work_node_ref w, work_occurrence w) b)
    (Hskip : forall ro b, In ro (input_visit input) -> Index.view_expr (snd ro) = None -> fo ro b = b) :
  fold_right fw init (forest_items forest) = fold_right fo init (input_visit input).
Proof.
  rewrite (fold_right_filter_skip fo occurrence_is_expr init (input_visit input)
             (fun ro b Hin Hf => Hskip ro b Hin (occurrence_is_expr_false_view ro Hf))).
  rewrite <- (forest_items_exact forest), fold_right_map.
  apply fold_ext_in. intros; apply Hagree.
Qed.

(* the total query matches the specification at the member's own occurrence, projected from the trace *)
Lemma total_forest_outcome_at_matches {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) :
  outcome_matches (index input) (work_node_ref (proj1_sig wm)) (work_occurrence (proj1_sig wm))
    (total_forest_outcome_at ot wm).
Proof. exact (trace_match (forest_items forest) (outcomes_acc ot) (outcomes_trace ot) (wm_suffix wm)). Qed.

(** each member's retained direct cause, projected from the trace with its authenticated prior state *)
Definition total_forest_outcome_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest)
  : RetainedMemberCause forest tnft (forest_items forest) (outcomes_acc ot) (wm_suffix wm) :=
  trace_retained_cause (forest_items forest) (outcomes_acc ot) (outcomes_trace ot) (wm_suffix wm).

(** the final-to-tail closure: a tail member's final outcome equals its outcome in the retained tail *)
Lemma final_operand_outcome {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (rest : list (Work input))
    (acc_rest : Accumulator forest tnft rest)
    (Hpreserve : forall (sm2 : SuffixMember forest rest) (Hlift : In (sm_work sm2) (forest_items forest)),
       accumulator_total acc_rest sm2 = accumulator_total (outcomes_acc ot) (exist _ (proj1_sig sm2) Hlift))
    (sm_op : SuffixMember forest rest) :
  total_forest_outcome_at ot (proj1_sig sm_op) = accumulator_total acc_rest sm_op.
Proof. symmetry. exact (Hpreserve sm_op (proj2_sig (proj1_sig sm_op))). Qed.

(** the retained cause and the final-to-tail closure for any member, projected off the trace as one object *)
Definition retained_conversion_closure {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest)
  : { rest : list (Work input) &
    { acc_rest : Accumulator forest tnft rest &
      ((StepCause forest tnft (proj1_sig wm) rest acc_rest (total_forest_outcome_at ot wm))
       * (forall sm_op : SuffixMember forest rest,
            total_forest_outcome_at ot (proj1_sig sm_op) = accumulator_total acc_rest sm_op))%type } }.
Proof.
  destruct (total_forest_outcome_cause ot wm) as [rest [acc_rest [[Hsplit stepc] Hpreserve]]].
  exists rest, acc_rest. split.
  - exact stepc.
  - intro sm_op. exact (final_operand_outcome ot rest acc_rest Hpreserve sm_op).
Defined.

(** the direct cause, projected by inverting the step cause, so no dependent-destruction axiom is needed *)
Lemma conversion_failure_cause_yields_step {p} {input : Input p} {forest : WorkForest input} {tnft}
    (current : Work input) (rest : list (Work input)) (acc_rest : Accumulator forest tnft rest)
    er2 tr2 opr2 t ci :
  StepCause forest tnft current rest acc_rest (ConversionFailure er2 tr2 opr2 t ci) ->
  exists ts x (step : ConversionStep forest current rest ts x) opf,
       work_expr current = Syntax.Convert ts x
    /\ accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf
    /\ er2 = work_expr_ref current
    /\ tr2 = conversion_target_node_ref (step_conversion step)
    /\ opr2 = work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step)))
    /\ t = fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))
    /\ ci = const_status opf
    /\ Typing.convert_constant t ci = None.
Proof.
  intro Hsc. remember (ConversionFailure er2 tr2 opr2 t ci) as ov eqn:Hov.
  destruct Hsc as [ ci0 Hnone Hconst | ts x step opf tc Hcur He Hop Hconv
                  | ts x step opf Hcur He Hop Hconv | ts x step Hcur He Hfail ];
    try discriminate Hov.
  injection Hov as Her2 Htr2 Hopr2 Ht Hci. subst.
  exists ts, x, step, opf.
  repeat split; (assumption || reflexivity).
Qed.

Lemma child_failure_cause_yields_member {p} {input : Input p} {forest : WorkForest input} {tnft}
    (current : Work input) (rest : list (Work input)) (acc_rest : Accumulator forest tnft rest) :
  StepCause forest tnft current rest acc_rest ChildFailure ->
  exists ts x (step : ConversionStep forest current rest ts x),
       work_expr current = Syntax.Convert ts x
    /\ outcome_is_fail (accumulator_total acc_rest (step_operand_suffix step)).
Proof.
  intro Hsc. remember ChildFailure as ov eqn:Hov.
  destruct Hsc as [ ci0 Hnone Hconst | ts x step opf tc Hcur He Hop Hconv
                  | ts x step opf Hcur He Hop Hconv | ts x step Hcur He Hfail ];
    try discriminate Hov.
  exists ts, x, step. split; assumption.
Qed.

Lemma conversion_success_cause_yields_step {p} {input : Input p} {forest : WorkForest input} {tnft}
    (current : Work input) (rest : list (Work input)) (acc_rest : Accumulator forest tnft rest)
    ts0 x0 f :
  work_expr current = Syntax.Convert ts0 x0 ->
  StepCause forest tnft current rest acc_rest (ExpressionSuccess f) ->
  (* the returned step is at the exact source parameters supplied, so no existential distinction survives *)
  exists (step : ConversionStep forest current rest ts0 x0) opf tc,
       accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf
    /\ Typing.convert_constant (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))))
         (const_status opf) = Some tc
    /\ f = MakeExpressionFact (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))) tc)
             (use_resolved_of_input (expression_ref_role (work_expr_ref current))
                (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))) tc)).
Proof.
  intros Hconvcur Hsc. remember (ExpressionSuccess f) as ov eqn:Hov.
  destruct Hsc as [ ci0 Hnone Hconst | ts x step opf tc Hcur He Hop Hconv
                  | ts x step opf Hcur He Hop Hconv | ts x step Hcur He Hfail ];
    try discriminate Hov.
  - (* LeafCause: leaf_outcome = ExpressionSuccess, but [current] is a conversion (has a child) — contradiction *)
    exfalso. rewrite Hconvcur in Hnone. cbn [Typing.expression_child] in Hnone. discriminate Hnone.
  - (* ConversionSuccessCause: identify the constructor's ts/x with the source ts0/x0 by Syntax.Convert injectivity *)
    assert (Hid : Syntax.Convert ts x = Syntax.Convert ts0 x0) by (rewrite <- He; exact Hconvcur).
    injection Hid as Hts Hx. subst ts0 x0.
    injection Hov as Hf. exists step, opf, tc.
    split; [ exact Hop | split; [ exact Hconv | exact (eq_sym Hf) ] ].
Qed.

(** an item's total outcome is determined by its occurrence's local shape, with no fail-open branch *)
Lemma total_forest_outcome_ok_of_fact {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) f :
  occurrence_expr_fact (work_occurrence (proj1_sig wm)) = Some f -> total_forest_outcome_at ot wm = ExpressionSuccess f.
Proof.
  intro Hf. pose proof (total_forest_outcome_at_matches ot wm) as Hm.
  destruct (total_forest_outcome_at ot wm) as [f'| er2 tr2 opr2 t ci |]; cbn [outcome_matches] in Hm.
  - rewrite Hf in Hm. injection Hm as Hm. rewrite Hm. reflexivity.
  - destruct Hm as [Hnone _]. rewrite Hf in Hnone. discriminate.
  - destruct Hm as [Hnone _]. rewrite Hf in Hnone. discriminate.
Qed.

Lemma total_forest_outcome_convfail_shape {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) ts x :
  Index.view_expr (work_occurrence (proj1_sig wm)) = Some (Syntax.Convert ts x) ->
  occurrence_expr_fact (work_occurrence (proj1_sig wm)) = None ->
  local_conv_failure (Syntax.Convert ts x) <> None ->
  exists er2 tr2 opr2 t ci, total_forest_outcome_at ot wm = ConversionFailure er2 tr2 opr2 t ci.
Proof.
  intros Hview Hnf Hlcf. pose proof (total_forest_outcome_at_matches ot wm) as Hm.
  destruct (total_forest_outcome_at ot wm) as [f| er2 tr2 opr2 t ci |]; cbn [outcome_matches] in Hm.
  - rewrite Hnf in Hm. discriminate.
  - exists er2, tr2, opr2, t, ci. reflexivity.
  - destruct Hm as [_ [e [Hve Hlcfe]]]. rewrite Hview in Hve. injection Hve as He. subst e.
    destruct (Hlcf Hlcfe).
Qed.

Lemma total_forest_outcome_childfail_shape {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) ts x :
  Index.view_expr (work_occurrence (proj1_sig wm)) = Some (Syntax.Convert ts x) ->
  occurrence_expr_fact (work_occurrence (proj1_sig wm)) = None ->
  local_conv_failure (Syntax.Convert ts x) = None ->
  total_forest_outcome_at ot wm = ChildFailure.
Proof.
  intros Hview Hnf Hlcf. pose proof (total_forest_outcome_at_matches ot wm) as Hm.
  destruct (total_forest_outcome_at ot wm) as [f| er2 tr2 opr2 t ci |];
    cbn [outcome_matches outcome_convfail_ev] in Hm.
  - rewrite Hnf in Hm. discriminate.
  - destruct Hm as [_ [_ [[e [Hve Hlcfe]] _]]]. rewrite Hview in Hve. injection Hve as He. subst e.
    rewrite Hlcf in Hlcfe. discriminate.
  - reflexivity.
Qed.

(** the retained member list, built once, so the folds can use the total query without a fail-open branch *)
Fixpoint members_go {p} {input : Input p} (forest : WorkForest input)
    (sub : list (Work input)) : (forall w, In w sub -> In w (forest_items forest)) -> list (WorkMember forest) :=
  match sub as s return ((forall w, In w s -> In w (forest_items forest)) -> list (WorkMember forest)) with
  | [] => fun _ => []
  | y :: ys => fun H => exist _ y (H y (or_introl eq_refl))
                        :: members_go forest ys (fun w Hw => H w (or_intror Hw))
  end.
Definition members_of {p} {input : Input p} (forest : WorkForest input) : list (WorkMember forest) :=
  members_go forest (forest_items forest) (fun w H => H).
Lemma members_go_proj {p} {input : Input p} (forest : WorkForest input) sub H :
  map (fun m => proj1_sig m) (members_go forest sub H) = sub.
Proof.
  revert H. induction sub as [|y ys IH]; intro H; [reflexivity|].
  cbn [members_go map]. rewrite (IH (fun w Hw => H w (or_intror Hw))). reflexivity.
Qed.
Lemma members_of_proj {p} {input : Input p} (forest : WorkForest input) :
  map (fun m => proj1_sig m) (members_of forest) = forest_items forest.
Proof. apply members_go_proj. Qed.

(** the fact projection folds the retained members through the total query, and equals the specification *)
Definition forest_fact_step {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) (m : Index.KeyMap.t ExpressionFact)
  : Index.KeyMap.t ExpressionFact :=
  match total_forest_outcome_at ot wm with
  | ExpressionSuccess f => Index.KeyMap.add (Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))) f m
  | _ => m
  end.
Definition forest_facts {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) (ot : Outcomes forest tnft) : Index.KeyMap.t ExpressionFact :=
  fold_right (forest_fact_step ot) (Index.KeyMap.empty ExpressionFact) (members_of forest).

Lemma add_occ_fact_nonexpr {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence) m :
  Index.view_expr (snd ro) = None -> add_occ_fact ro m = m.
Proof. intro H. unfold add_occ_fact. rewrite (occurrence_expr_fact_none_nonexpr (snd ro) H). reflexivity. Qed.

Lemma forest_fact_step_eq {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) m :
  forest_fact_step ot wm m
  = add_occ_fact (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)) m.
Proof.
  unfold forest_fact_step, add_occ_fact. cbn [fst snd].
  pose proof (total_forest_outcome_at_matches ot wm) as Hm.
  pose proof (outcome_matches_proj (index input) (work_node_ref (proj1_sig wm)) (work_occurrence (proj1_sig wm))
                (total_forest_outcome_at ot wm) Hm) as Hpf.
  destruct (total_forest_outcome_at ot wm) as [f|c1 c2 c3 c4 c5| ];
    cbn [outcome_proj_fact] in Hpf; rewrite Hpf; reflexivity.
Qed.

(** the source-determined fact map, which the production projection is proved equal to *)
Definition program_expr_facts (p : Syntax.Program) : Index.KeyMap.t ExpressionFact :=
  fold_right add_occ_fact (Index.KeyMap.empty ExpressionFact) (program_visit p).

(* §9/§2.7 the forest fact projection EQUALS the source specification, over the SAME retained work order. *)
Lemma forest_facts_eq_spec {p} {input : Input p} (forest : WorkForest input)
    (tnft : TypeNameFacts p) (ot : Outcomes forest tnft) :
  forest_facts forest tnft ot = program_expr_facts p.
Proof.
  unfold forest_facts.
  transitivity (fold_right (fun w m => add_occ_fact (work_node_ref w, work_occurrence w) m)
                  (Index.KeyMap.empty ExpressionFact) (forest_items forest)).
  - rewrite <- (members_of_proj forest), fold_right_map.
    apply fold_ext_in. intros wm b _. apply forest_fact_step_eq.
  - rewrite (forest_fold forest (fun w m => add_occ_fact (work_node_ref w, work_occurrence w) m) (@add_occ_fact p)
               (Index.KeyMap.empty ExpressionFact)
               (fun w b => eq_refl) (fun ro b _ Hvnone => add_occ_fact_nonexpr ro b Hvnone)).
    unfold program_expr_facts. rewrite (input_visit_ok input). reflexivity.
Qed.

Lemma program_expr_facts_eq_spec (p : Syntax.Program) :
  program_expr_facts p = fold_right add_occ_fact (Index.KeyMap.empty ExpressionFact) (program_visit p).
Proof. reflexivity. Qed.

(** the fact at a visited reference's key is exactly that occurrence's fact *)
Lemma program_expr_facts_find (p : Syntax.Program) (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (program_visit p) ->
  Index.KeyMap.find (Index.Snapshot.node_ref_key r) (program_expr_facts p) = occurrence_expr_fact occ.
Proof.
  intro Hin. rewrite program_expr_facts_eq_spec. apply fold_facts_find; [ apply program_visit_key_nodup | exact Hin ].
Qed.

(** every key with an entry is a visited occurrence's, so a forged entry is unrepresentable *)
Lemma fold_add_occ_fact_domain {p} (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) k f :
  Index.KeyMap.find k (fold_right add_occ_fact (Index.KeyMap.empty ExpressionFact) l) = Some f ->
  exists ro, In ro l /\ Index.Snapshot.node_ref_key (fst ro) = k /\ occurrence_expr_fact (snd ro) = Some f.
Proof.
  induction l as [|ro rest IH]; intro Hf.
  - rewrite Index.KeyFacts.empty_o in Hf; discriminate Hf.
  - cbn [fold_right] in Hf. unfold add_occ_fact in Hf.
    destruct (occurrence_expr_fact (snd ro)) as [f0|] eqn:Ef.
    + destruct (Index.key_eq_dec (Index.Snapshot.node_ref_key (fst ro)) k) as [He|Hne].
      * subst k. rewrite Index.key_map_add_equal in Hf. injection Hf as <-.
        exists ro. split; [left; reflexivity | split; [reflexivity | exact Ef]].
      * rewrite Index.key_map_add_unequal in Hf by exact Hne.
        destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
    + destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Lemma program_expr_facts_domain (p : Syntax.Program) k f :
  Index.KeyMap.find k (program_expr_facts p) = Some f ->
  exists (r : Index.Snapshot.NodeRef p) occ, In (r, occ) (program_visit p)
    /\ Index.Snapshot.node_ref_key r = k /\ occurrence_expr_fact occ = Some f.
Proof.
  rewrite program_expr_facts_eq_spec. intro Hf.
  destruct (fold_add_occ_fact_domain (program_visit p) k f Hf) as [[r occ] [Hin [Hk Hfe]]].
  exists r, occ. cbn [fst snd] in *. split; [exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Record ExpressionFactTable (p : Syntax.Program) (ip : Index.Program p) : Type := MakeExpressionFactTable {
  fact_table_map      : Index.KeyMap.t ExpressionFact ;
  fact_table_domain   : forall k f, Index.KeyMap.find k fact_table_map = Some f ->
                   exists (r : Index.Snapshot.NodeRef p) occ, In (r, occ) (program_visit p)
                     /\ Index.Snapshot.node_ref_key r = k /\ occurrence_expr_fact occ = Some f ;
  fact_table_complete : forall r occ, In (r, occ) (program_visit p) ->
                   Index.KeyMap.find (Index.Snapshot.node_ref_key r) fact_table_map = occurrence_expr_fact occ
}.
Arguments MakeExpressionFactTable {p ip} _ _ _.
Arguments fact_table_map {p ip} _.
Arguments fact_table_domain {p ip} _.
Arguments fact_table_complete {p ip} _.

(* the expression decision: every println argument resolves exactly when the program types *)

Lemma forallb_flat_map {A B} (f : B -> bool) (g : A -> list B) (l : list A) :
  forallb f (flat_map g l) = forallb (fun x => forallb f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite forallb_app, IH; reflexivity]. Qed.

(* the per-occurrence typing predicate lives here, the sole meeting point of index identity and typing *)
Definition occurrence_arg_typedb (o : Index.Occurrence) : bool :=
  match Index.occurrence_role o with
  | Index.PrintlnArgument _ => match Index.view_expr o with Some e => expression_typedb Typing.PrintlnArgument e | None => true end
  | _ => true
  end.

(* a conversion's TYPE-NAME occurrence (kind Index.TypeNameKind, no expression view) is vacuously typed. *)
Lemma occurrence_arg_typedb_typename : forall ts par sub,
  occurrence_arg_typedb (Index.MakeOccurrence Index.TypeNameKind (Index.TypeNameView ts) (Some par) Index.ConversionTarget sub) = true.
Proof. reflexivity. Qed.

Lemma occurrence_arg_typedb_operand : forall e par sub,
  occurrence_arg_typedb (Index.MakeOccurrence Index.ExpressionKind (Index.ExpressionView e) (Some par) Index.ConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occurrence_arg_typedb_printlnarg : forall e par aidx sub,
  occurrence_arg_typedb (Index.MakeOccurrence Index.ExpressionKind (Index.ExpressionView e) (Some par) (Index.PrintlnArgument aidx) sub)
  = expression_typedb Typing.PrintlnArgument e.
Proof. reflexivity. Qed.

(* every occurrence inside a conversion operand carries role [Index.ConversionOperand], hence is vacuously typed. *)
Lemma occurrences_expr_operand_true : forall e parent me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_expr parent Index.ConversionOperand me e) = true.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent me; cbn [Index.occurrences_expr forallb snd].
  1,2,3,4,5,6: rewrite occurrence_arg_typedb_operand; reflexivity.
  rewrite occurrence_arg_typedb_operand, occurrence_arg_typedb_typename, !Bool.andb_true_l; apply IHx.
Qed.

(* one println argument's occurrence stream types exactly as the existing [expression_typedb Typing.PrintlnArgument]. *)
Lemma occurrences_arg_typedb_eq : forall e parent aidx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_arg parent aidx me e) = expression_typedb Typing.PrintlnArgument e.
Proof.
  intros e parent aidx me. unfold Index.occurrences_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [Index.occurrences_expr forallb snd]; rewrite occurrence_arg_typedb_printlnarg.
  1,2,3,4,5,6: apply Bool.andb_true_r.
  rewrite occurrence_arg_typedb_typename, occurrences_expr_operand_true, ?Bool.andb_true_r, ?Bool.andb_true_l; reflexivity.
Qed.

Lemma occurrences_args_typedb_eq : forall es parent aidx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_args parent aidx me es)
  = forallb (expression_typedb Typing.PrintlnArgument) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me.
  - reflexivity.
  - cbn [Index.occurrences_args]. rewrite forallb_app, occurrences_arg_typedb_eq, IH. reflexivity.
Qed.

Lemma occurrences_stmt_typedb_eq : forall s parent sidx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_stmt parent sidx me s) = stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [Index.occurrences_stmt forallb snd occurrence_arg_typedb Index.occurrence_role].
  rewrite occurrences_args_typedb_eq. reflexivity.
Qed.

Lemma occurrences_stmts_typedb_eq : forall ss parent sidx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_stmts parent sidx me ss) = forallb stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me.
  - reflexivity.
  - cbn [Index.occurrences_stmts]. rewrite forallb_app, occurrences_stmt_typedb_eq, IH. reflexivity.
Qed.

Lemma occurrences_decl_typedb_eq : forall d parent didx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_decl parent didx me d) = decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [Index.occurrences_decl forallb snd occurrence_arg_typedb Index.occurrence_role].
  rewrite occurrences_stmts_typedb_eq. reflexivity.
Qed.

Lemma occurrences_decls_typedb_eq : forall ds parent didx me,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_decls parent didx me ds) = forallb decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me.
  - reflexivity.
  - cbn [Index.occurrences_decls]. rewrite forallb_app, occurrences_decl_typedb_eq, IH. reflexivity.
Qed.

(* a file's whole occurrence stream types exactly as the existing per-file decision *)
Lemma occurrences_file_typedb_eq : forall f,
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.occurrences_file f) = source_file_typedb f.
Proof.
  intros f. unfold Index.occurrences_file. destruct (Syntax.imports f) as [|i tl] eqn:E.
  - cbn [forallb snd occurrence_arg_typedb Index.occurrence_role].
    rewrite occurrences_decls_typedb_eq. unfold Typing.source_file_typedb, Typing.file_typedb. reflexivity.
  - destruct i.
Qed.

(** one file's argument occurrences resolve exactly when the file types *)
Lemma visit_file_arg_typedb {p} (fr : Index.Snapshot.FileRef p) :
  forallb (fun x => occurrence_arg_typedb (snd x)) (Index.Snapshot.visit_file fr)
  = source_file_typedb (Index.Snapshot.file_ref_source fr).
Proof.
  rewrite Typing.forallb_map_snd, Index.Snapshot.visit_file_snd, <- Typing.forallb_map_snd.
  apply occurrences_file_typedb_eq.
Qed.

(** the per-occurrence "argument resolves" check folded over the whole program. *)
Definition expression_all_ok (p : Syntax.Program) : bool :=
  forallb (fun x => occurrence_arg_typedb (snd x)) (program_visit p).

(** the expression decision is exactly program typing: no diagnostic exactly when every argument resolves *)
Lemma expression_all_ok_program_typedb (p : Syntax.Program) : expression_all_ok p = program_typedb p.
Proof.
  unfold expression_all_ok. rewrite program_visit_flat_map, forallb_flat_map. unfold Typing.program_typedb.
  apply Typing.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (Syntax.file_bindings_find (Syntax.files p) b Hb) as Hfind.
  destruct (Index.Snapshot.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_arg_typedb, Hsrc. reflexivity.
Qed.

Lemma expression_all_ok_iff_typed_program (p : Syntax.Program) :
  expression_all_ok p = true <-> Typing.Program predeclared_type p.
Proof. rewrite expression_all_ok_program_typedb. apply Typing.program_typedb_iff. Qed.

(* the package decision: the two factored roots and their direct reflections *)

Definition semantic_ok_b (p : Syntax.Program) : bool := expression_all_ok p && source_spec_package_rules_b p.

Lemma semantic_ok_b_source_spec_valid_b (p : Syntax.Program) : semantic_ok_b p = source_spec_valid_b p.
Proof. unfold semantic_ok_b, source_spec_valid_b. rewrite expression_all_ok_program_typedb. reflexivity. Qed.

(* the expression diagnostic per occurrence: its primary is the occurrence's own reference, never minted *)

Definition default_target_of (c : Typing.Constant) : Typing.SemanticType :=
  match c with
  | Typing.BoolConstant _    => Typing.BoolType
  | Typing.IntegerConstant _     => Typing.IntegerType Integer.Int
  | Typing.FloatConstant _   => Typing.FloatType F64
  | Typing.ComplexConstant _ => Typing.ComplexType C128
  | Typing.StringConstant _  => Typing.StringType
  end.

(** the conversion syntax projection: a conversion whose target name resolves to the reported type *)
Definition conv_targets (e : Syntax.Expr) : option (Typing.SemanticType * Syntax.Expr) :=
  match e with
  | Syntax.Convert ts x => Some (predeclared_type ts, x)
  | _             => None
  end.

(** a local conversion failure denotes its code: the syntax, the operand status, and a rejecting conversion *)
Lemma local_conv_failure_char (e : Syntax.Expr) (t : Typing.SemanticType) (ci : Typing.ConstantInfo) :
  local_conv_failure e = Some (t, ci) ->
  exists x, conv_targets e = Some (t, x) /\ constant_info x = Some ci /\ Typing.convert_constant t ci = None.
Proof.
  intro H. destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate H; cbn [local_conv_failure] in H;
    (destruct (constant_info x) as [ci'|] eqn:Ex; [| discriminate H];
     destruct (Typing.convert_constant _ ci') as [c'|] eqn:Ec; [ discriminate H | injection H as Ht Hc; subst ];
     exists x; cbn [conv_targets]; rewrite Ex; split; [reflexivity | split; [reflexivity | exact Ec]]).
Qed.

(** a println-argument occurrence whose exact untyped constant does not default — returns (constant, default). *)
Definition arg_default_failure (occ : Index.Occurrence) (e : Syntax.Expr) : option (Typing.Constant * Typing.SemanticType) :=
  match Index.occurrence_role occ with
  | Index.PrintlnArgument _ =>
      match constant_info e with
      | Some (Typing.UntypedInfo c) => match Typing.default_constant c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None
      end
  | _ => None
  end.

(** the conversion test reads only the delivered occurrence, with no recovery step of its own *)
Definition is_conversion_occ (occ : Index.Occurrence) : bool :=
  match Index.view_expr occ with
  | Some (Syntax.Convert _ _) => true
  | _ => false
  end.

(** one forward pass carries the open-conversion stack, so each occurrence's context is delivered *)
Fixpoint annotate_encl {p} (idx : Index.Snapshot.Syntax p)
    (stack : list (Index.ExprRef p * positive))
    (stream : list (Index.Snapshot.NodeRef p * Index.Occurrence))
    : list ((Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p)) :=
  match stream with
  | [] => []
  | ro :: rest =>
      let open := filter (fun e => Pos.leb (Index.Snapshot.node_ref_local (fst ro)) (snd e)) stack in
      let stack' := match Index.as_expr idx (fst ro) with
                    | Some er => if is_conversion_occ (snd ro)
                                 then (er, Index.Snapshot.node_subtree_end idx (fst ro)) :: open
                                 else open
                    | None => open
                    end in
      (ro, map fst open) :: annotate_encl idx stack' rest
  end.

(* the enclosing-conversion stack still open at an occurrence, shared with the typed-work annotation *)
Definition estack_open {p} (idx : Index.Snapshot.Syntax p)
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
    (stack : list (Index.ExprRef p * positive)) : list (Index.ExprRef p * positive) :=
  filter (fun e => Pos.leb (Index.Snapshot.node_ref_local (fst ro)) (snd e)) stack.

(* the annotation's step made explicit: pop, record, then push a conversion's own reference *)
Lemma annotate_encl_cons {p} (idx : Index.Snapshot.Syntax p) stack ro rest :
  annotate_encl idx stack (ro :: rest)
  = (ro, map fst (estack_open idx ro stack))
    :: annotate_encl idx
         (match Index.as_expr idx (fst ro) with
          | Some er => if is_conversion_occ (snd ro)
                       then (er, Index.Snapshot.node_subtree_end idx (fst ro)) :: estack_open idx ro stack
                       else estack_open idx ro stack
          | None => estack_open idx ro stack
          end) rest.
Proof. reflexivity. Qed.

Lemma flat_map_map {A B C} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [map flat_map]. rewrite IH. reflexivity. Qed.

(** the annotation preserves the underlying occurrence stream (it only attaches context). *)
Lemma annotate_encl_fst {p} (idx : Index.Snapshot.Syntax p) stack stream :
  map fst (annotate_encl idx stack stream) = stream.
Proof.
  revert stack; induction stream as [|ro rest IH]; intro stack; [reflexivity|].
  cbn [annotate_encl map]. rewrite IH. reflexivity.
Qed.

(* every open stack entry is a genuine conversion reference with its recorded subtree end *)
Definition estack_ok {p} (idx : Index.Snapshot.Syntax p) (stack : list (Index.ExprRef p * positive)) : Prop :=
  forall er se, In (er, se) stack ->
    Index.as_expr idx (Index.erase_ref er) = Some er
    /\ is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = true
    /\ Index.Snapshot.node_subtree_end idx (Index.erase_ref er) = se.

(* filtering preserves the stack invariant. *)
Lemma estack_ok_filter {p} (idx : Index.Snapshot.Syntax p) P stack :
  estack_ok idx stack -> estack_ok idx (filter P stack).
Proof. intros H er se Hin. apply filter_In in Hin. exact (H er se (proj1 Hin)). Qed.

(** every delivered enclosing reference is a conversion whose subtree strictly contains the occurrence *)
Lemma annotate_encl_ctx_sound {p} (idx : Index.Snapshot.Syntax p) : forall stream stack,
  StronglySorted (fun x y => Pos.lt (Index.Snapshot.node_ref_local (fst x)) (Index.Snapshot.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = Index.Snapshot.source_occurrence_of_ref (fst ro)) ->
  estack_ok idx stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref er)) (Index.Snapshot.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
  forall er, In er ctx ->
    is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = true
    /\ Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref er)) (Index.Snapshot.node_ref_local (fst ro))
    /\ Pos.le (Index.Snapshot.node_ref_local (fst ro)) (Index.Snapshot.node_subtree_end idx (Index.erase_ref er)).
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hstk Hbnd roc ctx Hin er Her; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (Index.Snapshot.node_ref_local (fst ro0)) (snd e)) stack) in *.
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
      destruct (Index.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- intros e s [Hh | Ht].
           ++ injection Hh as He Hs. subst e s.
              rewrite (Index.erase_as_kind idx (fst ro0) Index.ExpressionKind er0 Ea).
              split; [exact Ea | split; [ rewrite <- (Hval ro0 (or_introl eq_refl)); exact Hc0 | reflexivity ]].
           ++ exact (estack_ok_filter idx _ stack Hstk e s Ht).
        -- exact (estack_ok_filter idx _ stack Hstk).
      * exact (estack_ok_filter idx _ stack Hstk).
    + (* the bound for rest: stack' entries below rest's locals *)
      intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (Index.Snapshot.node_ref_local (fst ro0)) (Index.Snapshot.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (Index.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- destruct Hes as [Hh | Ht].
           ++ injection Hh as He Hs. subst e.
              rewrite (Index.erase_as_kind idx (fst ro0) Index.ExpressionKind er0 Ea). exact Hlt0.
           ++ pose proof Ht as Ht'. apply filter_In in Ht'.
              exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
        -- pose proof Hes as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma strongly_sorted_filter {A} (R : A -> A -> Prop) (P : A -> bool) l :
  StronglySorted R l -> StronglySorted R (filter P l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd]. cbn [filter].
  destruct (P a); [| apply IH; exact Hs].
  constructor; [apply IH; exact Hs|]. rewrite Forall_forall in Hhd |- *.
  intros x Hx. apply filter_In in Hx. apply Hhd. exact (proj1 Hx).
Qed.

Lemma strongly_sorted_map {A B} (R : B -> B -> Prop) (f : A -> B) l :
  StronglySorted (fun x y => R (f x) (f y)) l -> StronglySorted R (map f l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map]. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [x [Hxy Hx]]. subst y. exact (Hhd x Hx).
Qed.

Lemma strongly_sorted_no_duplicates {A} (R : A -> A -> Prop) l :
  (forall a, ~ R a a) -> StronglySorted R l -> NoDup l.
Proof.
  intro Hirr. induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [| apply IH; exact Hs].
  intro Hina. rewrite Forall_forall in Hhd. exact (Hirr a (Hhd a Hina)).
Qed.

Lemma strongly_sorted_impl_in {A} (R R' : A -> A -> Prop) l :
  (forall x y, In x l -> In y l -> R x y -> R' x y) -> StronglySorted R l -> StronglySorted R' l.
Proof.
  intros Himp H. induction l as [|a l IH]; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor.
  - apply IH; [| exact Hs]. intros x y Hx Hy. apply Himp; right; assumption.
  - rewrite Forall_forall in Hhd |- *. intros x Hx. apply Himp; [left; reflexivity | right; exact Hx | exact (Hhd x Hx)].
Qed.

Lemma strongly_sorted_app {A} (R : A -> A -> Prop) l1 l2 :
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

(* the stack is same-file and strictly descending, so its projection is nearest-first and duplicate-free *)
Definition estack_wf {p} (idx : Index.Snapshot.Syntax p) (fr : Index.Snapshot.FileRef p)
    (stack : list (Index.ExprRef p * positive)) : Prop :=
  Forall (fun e => Index.Snapshot.node_ref_file (Index.erase_ref (fst e)) = fr) stack
  /\ StronglySorted (fun x y => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref (fst y)))
                                       (Index.Snapshot.node_ref_local (Index.erase_ref (fst x)))) stack.

Lemma estack_wf_filter {p} (idx : Index.Snapshot.Syntax p) fr P stack :
  estack_wf idx fr stack -> estack_wf idx fr (filter P stack).
Proof.
  intros [Hf Hs]. split.
  - apply Forall_forall. intros e He. apply filter_In in He. rewrite Forall_forall in Hf. exact (Hf e (proj1 He)).
  - apply strongly_sorted_filter; assumption.
Qed.

(** the delivered context is same-file, nearest-first and duplicate-free over a per-file block *)
Lemma annotate_encl_ctx_wf {p} (idx : Index.Snapshot.Syntax p) (fr : Index.Snapshot.FileRef p) :
  forall stream stack,
  StronglySorted (fun x y => Pos.lt (Index.Snapshot.node_ref_local (fst x)) (Index.Snapshot.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = Index.Snapshot.source_occurrence_of_ref (fst ro) /\ Index.Snapshot.node_ref_file (fst ro) = fr) ->
  estack_wf idx fr stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref er)) (Index.Snapshot.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
    Forall (fun er => Index.Snapshot.node_ref_file (Index.erase_ref er) = fr) ctx
    /\ StronglySorted (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b)) (Index.Snapshot.node_ref_local (Index.erase_ref a))) ctx.
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hwf Hbnd roc ctx Hin; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (Index.Snapshot.node_ref_local (fst ro0)) (snd e)) stack) in *.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
  assert (Hwfopen : estack_wf idx fr open) by (apply estack_wf_filter; exact Hwf).
  destruct Hin as [Heq | Hin].
  - injection Heq as Hro Hctx. subst roc ctx. destruct Hwfopen as [Hf Hs].
    split.
    + rewrite Forall_forall. intros er Herin. apply in_map_iff in Herin.
      destruct Herin as [[e s] [Hes Hin']]. cbn [fst] in Hes. subst er.
      rewrite Forall_forall in Hf. exact (Hf (e, s) Hin').
    + apply (strongly_sorted_map (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b))
                                                   (Index.Snapshot.node_ref_local (Index.erase_ref a)))
              fst open). exact Hs.
  - refine (IH _ Hsort0 (fun ro' Hr => Hval ro' (or_intror Hr)) _ _ roc ctx Hin).
    + destruct (Index.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ]; try (exact Hwfopen).
      destruct Hwfopen as [Hf Hs]. split.
      * constructor; [| exact Hf]. cbn [fst].
        rewrite (Index.erase_as_kind idx (fst ro0) Index.ExpressionKind er0 Ea).
        exact (proj2 (Hval ro0 (or_introl eq_refl))).
      * constructor; [exact Hs|]. apply Forall_forall. intros [e s] He. cbn [fst].
        rewrite (Index.erase_as_kind idx (fst ro0) Index.ExpressionKind er0 Ea).
        pose proof He as He'. apply filter_In in He'.
        exact (Hbnd ro0 e s (or_introl eq_refl) (proj1 He')).
    + intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (Index.Snapshot.node_ref_local (fst ro0)) (Index.Snapshot.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (Index.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ].
      * destruct Hes as [Hh | Ht].
        -- injection Hh as He Hs. subst e.
           rewrite (Index.erase_as_kind idx (fst ro0) Index.ExpressionKind er0 Ea). exact Hlt0.
        -- pose proof Ht as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma strongly_sorted_map_inv {A B} (R : B -> B -> Prop) (f : A -> B) (l : list A) :
  StronglySorted R (map f l) -> StronglySorted (fun x y => R (f x) (f y)) l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map] in H. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros x Hx. apply Hhd. exact (in_map f l x Hx).
Qed.

Definition annotate_program {p} (idx : Index.Snapshot.Syntax p)
  : list ((Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p)) :=
  flat_map (annotate_encl idx []) (program_blocks p).

(** the same soundness across the whole program *)
Lemma annotate_program_ctx_sound {p} (idx : Index.Snapshot.Syntax p) : forall ro ctx er,
  In (ro, ctx) (annotate_program idx) -> In er ctx ->
  is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = true
  /\ Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref er)) (Index.Snapshot.node_ref_local (fst ro))
  /\ Pos.le (Index.Snapshot.node_ref_local (fst ro)) (Index.Snapshot.node_subtree_end idx (Index.erase_ref er)).
Proof.
  intros ro ctx er Hin Her. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold program_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  refine (annotate_encl_ctx_sound idx (Index.Snapshot.visit_file fr) [] _ _ _ _ ro ctx Hin er Her).
  - apply strongly_sorted_map_inv. exact (Index.Snapshot.visit_file_order p fr).
  - intros [r occ] Hro. destruct (Index.Snapshot.visit_file_view p fr r occ Hro) as [Ho _]. exact Ho.
  - intros er0 se [].
  - intros ro0 er0 se _ [].
Qed.

(** the whole-program nested scar is SAME-FILE (as the primary), NEAREST-FIRST, and DUPLICATE-FREE. *)
Lemma annotate_program_ctx_wf {p} (idx : Index.Snapshot.Syntax p) : forall ro ctx,
  In (ro, ctx) (annotate_program idx) ->
  Forall (fun er => Index.Snapshot.node_ref_file (Index.erase_ref er) = Index.Snapshot.node_ref_file (fst ro)) ctx
  /\ StronglySorted (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b)) (Index.Snapshot.node_ref_local (Index.erase_ref a))) ctx
  /\ NoDup ctx.
Proof.
  intros ro ctx Hin. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold program_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  assert (Hroin : In ro (Index.Snapshot.visit_file fr))
    by (rewrite <- (annotate_encl_fst idx [] (Index.Snapshot.visit_file fr)); exact (in_map fst _ _ Hin)).
  assert (Hrf : Index.Snapshot.node_ref_file (fst ro) = fr).
  { destruct ro as [r occ]. destruct (Index.Snapshot.visit_file_view p fr r occ Hroin) as [_ Hf]. exact Hf. }
  assert (Hprops : Forall (fun er => Index.Snapshot.node_ref_file (Index.erase_ref er) = fr) ctx
                 /\ StronglySorted (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b))
                                                      (Index.Snapshot.node_ref_local (Index.erase_ref a))) ctx).
  { refine (annotate_encl_ctx_wf idx fr (Index.Snapshot.visit_file fr) [] _ _ _ _ ro ctx Hin).
    - apply strongly_sorted_map_inv. exact (Index.Snapshot.visit_file_order p fr).
    - intros [r occ] Hro. destruct (Index.Snapshot.visit_file_view p fr r occ Hro) as [Ho Hf]. split; assumption.
    - split; constructor.
    - intros ro0 er0 se _ []. }
  destruct Hprops as [Hfile Hss].
  rewrite Hrf. split; [exact Hfile | split; [exact Hss |]].
  exact (strongly_sorted_no_duplicates _ ctx (fun a => Pos.lt_irrefl _) Hss).
Qed.

Lemma annotate_program_fst {p} (idx : Index.Snapshot.Syntax p) :
  map fst (annotate_program idx) = program_visit p.
Proof.
  unfold annotate_program, program_visit.
  induction (program_blocks p) as [|b L IH]; [reflexivity|].
  cbn [flat_map concat]. rewrite map_app, annotate_encl_fst, IH. reflexivity.
Qed.

(** an occurrence's diagnostic, anchored at its own reference, with its context delivered not recomputed *)
Definition occurrence_expr_diags {p} (idx : Index.Snapshot.Syntax p) (outer : list (Index.ExprRef p))
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence) : list (DiagnosticReason p) :=
  match Index.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match Index.view_expr (snd ro) with
      | None => []
      | Some e =>
          match local_conv_failure e with
          | Some (t, ci) =>
              match conversion_target_ref idx er with
              | Some tr =>
                  match conversion_operand_ref idx er with
                  | Some opr => [ InvalidConversion er tr opr outer t ci ]
                  | None => []   (* provably dead: a live conversion always mints its operand ref *)
                  end
              | None => []   (* provably dead: a live conversion always mints its target ref *)
              end
          | None =>
              match arg_default_failure (snd ro) e with
              | Some (c, dt) => [ DefaultNotRepresentable er c dt ]
              | None => []
              end
          end
      end
  end.

(** a local conversion failure genuinely fails the shared conversion at the reported target *)
Lemma local_conv_failure_sound : forall e t ci,
  local_conv_failure e = Some (t, ci) -> Typing.convert_constant t ci = None.
Proof.
  intros e t ci H. unfold local_conv_failure in H.
  destruct e as [b|n|n0|s|df|dcx| ts x ]; try discriminate H;
    (destruct (constant_info x) as [ci'|]; [| discriminate H];
     destruct (Typing.convert_constant _ ci') eqn:Ec; [ discriminate H | injection H as <- <-; exact Ec ]).
Qed.

(** an invalid-conversion diagnostic denotes its code end to end *)
Lemma occurrence_expr_diags_conv_sound {p} (idx : Index.Snapshot.Syntax p) ro outer er tr opr outer' t ci :
  In (InvalidConversion er tr opr outer' t ci) (occurrence_expr_diags idx outer ro) ->
  outer' = outer
  /\ Index.as_expr idx (fst ro) = Some er
  /\ conversion_target_ref idx er = Some tr
  /\ conversion_operand_ref idx er = Some opr
  /\ Typing.convert_constant t ci = None
  /\ exists e x, Index.view_expr (snd ro) = Some e /\ conv_targets e = Some (t, x) /\ constant_info x = Some ci.
Proof.
  intro Hin. unfold occurrence_expr_diags in Hin.
  destruct (Index.as_expr idx (fst ro)) as [er2|] eqn:Ea; [| destruct Hin].
  destruct (Index.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc.
  - destruct (conversion_target_ref idx er2) as [tr2|] eqn:Ectr; [| destruct Hin].
    destruct (conversion_operand_ref idx er2) as [opr2|] eqn:Ecor; [| destruct Hin].
    destruct Hin as [Heq|[]]. injection Heq as He Htr Hopr Ho Ht Hc. subst er2 tr2 opr2 t' ci'.
    destruct (local_conv_failure_char e t ci Elc) as [x [Hct [Hci Hcv]]].
    split; [ symmetry; exact Ho
           | split; [ reflexivity
                    | split; [ exact Ectr
                             | split; [ exact Ecor
                                      | split; [ exact Hcv
                                               | exists e, x; split; [reflexivity | split; [exact Hct | exact Hci]]]]]]].
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|];
      [ destruct Hin as [Heq|[]]; discriminate Heq | destruct Hin ].
Qed.

(** a default-not-representable diagnostic denotes its code end to end *)
Lemma occurrence_expr_diags_default_sound {p} (idx : Index.Snapshot.Syntax p) ro outer er c dt :
  In (DefaultNotRepresentable er c dt) (occurrence_expr_diags idx outer ro) ->
  Index.as_expr idx (fst ro) = Some er
  /\ (exists aidx, Index.occurrence_role (snd ro) = Index.PrintlnArgument aidx)
  /\ (exists e, Index.view_expr (snd ro) = Some e /\ constant_info e = Some (Typing.UntypedInfo c))
  /\ Typing.default_constant c = None
  /\ dt = default_target_of c.
Proof.
  intro Hin. unfold occurrence_expr_diags in Hin.
  destruct (Index.as_expr idx (fst ro)) as [er'|] eqn:Ea; [| destruct Hin].
  destruct (Index.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc;
    [ destruct (conversion_target_ref idx er') as [tr'|];
      [ destruct (conversion_operand_ref idx er') as [opr'|];
        [ destruct Hin as [Heq|[]]; discriminate Heq | destruct Hin ]
      | destruct Hin ] |].
  destruct (arg_default_failure (snd ro) e) as [[c' dt']|] eqn:Ead; [| destruct Hin].
  destruct Hin as [Heq|[]]. injection Heq as He Hc Hd. subst er' c' dt'.
  unfold arg_default_failure in Ead.
  destruct (Index.occurrence_role (snd ro)) as [ | | ai | si | ain | | ] eqn:Erole; try discriminate Ead.
  destruct (constant_info e) as [cinf|] eqn:Eci; try discriminate Ead.
  destruct cinf as [cc | ct tc]; [| discriminate Ead].
  destruct (Typing.default_constant cc) eqn:Edc; [ discriminate Ead | injection Ead as Hcc Hdtc ]. subst c dt.
  split; [ reflexivity
         | split; [ exists ain; reflexivity
                  | split; [ exists e; split; [reflexivity | exact Eci]
                           | split; [ exact Edc | reflexivity ]]]].
Qed.

(* the diagnostic step projects each retained item's stored outcome, keyed by the work's own reference *)

Lemma local_conv_failure_const_none e t ci : local_conv_failure e = Some (t, ci) -> constant_info e = None.
Proof.
  intro H. destruct e as [ b|n1|n2|s| df | dcx | ts x ]; cbn [local_conv_failure] in H; try discriminate H.
  destruct (constant_info x) as [cix|] eqn:Ex; [| discriminate H].
  destruct (Typing.convert_constant (predeclared_type ts) cix) as [tc|] eqn:Ecv; [ discriminate H |].
  injection H as <- <-. rewrite const_info_conv_eq, Ex, Ecv. reflexivity.
Qed.

Lemma flat_map_ext_in {A B} (f g : A -> list B) (l : list A) :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [flat_map]. rewrite (H a (or_introl eq_refl)), IH by (intros a' Ha'; apply H; right; exact Ha'). reflexivity.
Qed.

(* the production diagnostics: the total projection over the one-pass annotated stream *)
Definition expression_diags {p} (idx : Index.Snapshot.Syntax p) : list (DiagnosticReason p) :=
  flat_map (fun roc => occurrence_expr_diags idx (snd roc) (fst roc)) (annotate_program idx).

Lemma expression_diags_eq_spec {p} (idx : Index.Snapshot.Syntax p) :
  expression_diags idx = flat_map (fun roc => occurrence_expr_diags idx (snd roc) (fst roc)) (annotate_program idx).
Proof. reflexivity. Qed.

(** the total diagnostic projection reads the work's own carried reference and its stored outcome *)
Definition work_default_failure (occ : Index.Occurrence) (f : ExpressionFact) : option (Typing.Constant * Typing.SemanticType) :=
  match Index.occurrence_role occ with
  | Index.PrintlnArgument _ =>
      match const_status f with
      | Typing.UntypedInfo c => match Typing.default_constant c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None end
  | _ => None
  end.
Lemma work_default_failure_eq (occ : Index.Occurrence) e f :
  constant_info e = Some (const_status f) -> work_default_failure occ f = arg_default_failure occ e.
Proof.
  intro Hci. unfold work_default_failure, arg_default_failure.
  destruct (Index.occurrence_role occ); try reflexivity. rewrite Hci. reflexivity.
Qed.
Lemma local_conv_failure_none_of_const e ci : constant_info e = Some ci -> local_conv_failure e = None.
Proof.
  intro Hci. destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc; [| reflexivity].
  exfalso. pose proof (local_conv_failure_const_none e t' ci' Elc) as Hcn. rewrite Hci in Hcn. discriminate Hcn.
Qed.

(* the specification diagnostic at a known reference and view, which the typed-work form matches *)
Lemma occurrence_expr_diags_of_ref {p} (idx : Index.Snapshot.Syntax p) (c : list (Index.ExprRef p))
    (r : Index.Snapshot.NodeRef p) occ (er : Index.ExprRef p) e :
  Index.as_expr idx r = Some er -> Index.view_expr occ = Some e ->
  occurrence_expr_diags idx c (r, occ)
  = match local_conv_failure e with
    | Some (t, ci) =>
        match conversion_target_ref idx er with
        | Some tr => match conversion_operand_ref idx er with
                     | Some opr => [ InvalidConversion er tr opr c t ci ]
                     | None => [] end
        | None => [] end
    | None => match arg_default_failure occ e with
              | Some (cst, dt) => [ DefaultNotRepresentable er cst dt ]
              | None => [] end
    end.
Proof. intros Hae Hv. unfold occurrence_expr_diags. cbn [fst snd]. rewrite Hae, Hv. reflexivity. Qed.

(* the specification is empty on a non-expression occurrence, which is why skipping it is source-determined *)
Lemma occurrence_expr_diags_nonexpr {p} (idx : Index.Snapshot.Syntax p) c
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence) :
  Index.view_expr (snd ro) = None -> occurrence_expr_diags idx c ro = [].
Proof.
  intro Hv. unfold occurrence_expr_diags. destruct (Index.as_expr idx (fst ro)) as [er|]; [ rewrite Hv | ]; reflexivity.
Qed.

(** the retained-work annotation zips the raw block's pop-and-push against the retained items as a cursor *)
Definition build_forest_awork {p} {input : Input p} (forest : WorkForest input) :
  forall (l : list (Index.Snapshot.NodeRef p * Index.Occurrence))
         (fitems : list (Work input)) (stack : list (Index.ExprRef p * positive)),
    map (fun w => (work_node_ref w, work_occurrence w)) fitems = filter occurrence_is_expr l ->
    (forall w, In w fitems -> In w (forest_items forest)) ->
    { aw : list (WorkMember forest * list (Index.ExprRef p)) |
        map (fun x => proj1_sig (fst x)) aw = fitems
        /\ (forall (X : Type) (d : (WorkMember forest * list (Index.ExprRef p)) -> list X)
               (dr : (Index.Snapshot.NodeRef p * Index.Occurrence) -> list (Index.ExprRef p) -> list X),
          (forall wm c, d (wm, c)
             = dr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)) c) ->
          (forall ro c, In ro l -> Index.view_expr (snd ro) = None -> dr ro c = []) ->
          flat_map d aw
          = flat_map (fun rc => dr (fst rc) (snd rc)) (annotate_encl (index input) stack l)) }.
Proof.
  induction l as [| [r occ] rest IH]; intros fitems stack Hfil Hmem.
  - exists nil. split.
    + cbn [filter] in Hfil. apply map_eq_nil in Hfil. rewrite Hfil. reflexivity.
    + intros X d dr Hagree Hempty. reflexivity.
  - pose (open := estack_open (index input) (r, occ) stack).
    destruct (Index.view_expr occ) as [e|] eqn:Hv.
    + destruct fitems as [| w frest].
      * exfalso. cbn [filter] in Hfil. rewrite (occurrence_is_expr_true r occ e Hv) in Hfil. discriminate Hfil.
      * cbn [map filter] in Hfil. rewrite (occurrence_is_expr_true r occ e Hv) in Hfil.
        injection Hfil as Hnr Hocc Hfrest.
        assert (Hae : Index.as_expr (index input) r = Some (work_expr_ref w))
          by (rewrite <- Hnr; exact (work_as_expr_exact w)).
        pose (stack' := if is_conversion_occ occ
                        then (work_expr_ref w, Index.Snapshot.node_subtree_end (index input) r) :: open
                        else open).
        destruct (IH frest stack' Hfrest (fun w' Hw' => Hmem w' (or_intror Hw'))) as [awrest [Hmemrest Hrest]].
        exists ((exist _ w (Hmem w (or_introl eq_refl)), map fst open) :: awrest). split.
        -- cbn [map fst proj1_sig]. rewrite Hmemrest. reflexivity.
        -- intros X d dr Hagree Hempty.
           rewrite (annotate_encl_cons (index input) stack (r, occ) rest).
           cbn [fst snd]. rewrite Hae. cbn [flat_map fst snd].
           rewrite Hagree. cbn [proj1_sig].
           rewrite Hnr, Hocc.
           rewrite (Hrest X d dr Hagree (fun ro' c Hin' Hv' => Hempty ro' c (or_intror Hin') Hv')).
           reflexivity.
    + destruct (IH fitems open
                  (ltac:(cbn [filter] in Hfil; rewrite (occurrence_is_expr_false r occ Hv) in Hfil; exact Hfil)) Hmem)
        as [awrest [Hmemrest Hrest]].
      exists awrest. split.
      * exact Hmemrest.
      * intros X d dr Hagree Hempty.
        rewrite (annotate_encl_cons (index input) stack (r, occ) rest).
        cbn [fst snd].
        assert (Hnc : is_conversion_occ occ = false) by (unfold is_conversion_occ; rewrite Hv; reflexivity).
        cbn [flat_map fst snd].
        rewrite (Hempty (r, occ) (map fst (estack_open (index input) (r, occ) stack)) (or_introl eq_refl) Hv).
        cbn [app].
        destruct (Index.as_expr (index input) r) as [er0|] eqn:Hae0;
          [ rewrite Hnc | ];
          exact (Hrest X d dr Hagree (fun ro' c Hin' Hv' => Hempty ro' c (or_intror Hin') Hv')).
Defined.

(* the annotation folds per block, with the stack reset at each, over the retained forest's own blocks *)
Definition build_forest_awork_blocks {p} {input : Input p} (forest : WorkForest input) :
  forall (blocks : list (list (Index.Snapshot.NodeRef p * Index.Occurrence)))
         (fbs : list (list (Work input))),
    map (map (fun w => (work_node_ref w, work_occurrence w))) fbs = map (filter occurrence_is_expr) blocks ->
    (forall w, In w (concat fbs) -> In w (forest_items forest)) ->
    { aw : list (WorkMember forest * list (Index.ExprRef p)) |
        map (fun x => proj1_sig (fst x)) aw = concat fbs
        /\ (forall (X : Type) (d : (WorkMember forest * list (Index.ExprRef p)) -> list X)
               (dr : (Index.Snapshot.NodeRef p * Index.Occurrence) -> list (Index.ExprRef p) -> list X),
          (forall wm c, d (wm, c)
             = dr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)) c) ->
          (forall ro c, In ro (concat blocks) -> Index.view_expr (snd ro) = None -> dr ro c = []) ->
          flat_map d aw
          = flat_map (fun rc => dr (fst rc) (snd rc)) (flat_map (annotate_encl (index input) []) blocks)) }.
Proof.
  induction blocks as [| blk rest IH]; intros fbs Hfil Hmem.
  - exists nil. split.
    + cbn [map] in Hfil. apply map_eq_nil in Hfil. rewrite Hfil. reflexivity.
    + intros X d dr Hagree Hempty. reflexivity.
  - destruct fbs as [| fblk fbrest]; [cbn [map] in Hfil; discriminate Hfil |].
    cbn [map] in Hfil. injection Hfil as Hblk Hrestfil. cbn [concat] in Hmem.
    destruct (build_forest_awork forest blk fblk [] Hblk
                (fun w Hw => Hmem w (in_or_app fblk (concat fbrest) w (or_introl Hw)))) as [awblk [Hmemblk Hblkeq]].
    destruct (IH fbrest Hrestfil (fun w Hw => Hmem w (in_or_app fblk (concat fbrest) w (or_intror Hw))))
      as [awrest [Hmemrest Hrest]].
    exists (awblk ++ awrest). split.
    + cbn [concat]. rewrite <- Hmemblk, <- Hmemrest, map_app. reflexivity.
    + intros X d dr Hagree Hempty.
      cbn [flat_map]. rewrite flat_map_app, flat_map_app.
      rewrite (Hblkeq X d dr Hagree
                 (fun ro c Hin Hv => Hempty ro c (in_or_app blk (concat rest) ro (or_introl Hin)) Hv)).
      rewrite (Hrest X d dr Hagree
                 (fun ro c Hin Hv => Hempty ro c (in_or_app blk (concat rest) ro (or_intror Hin)) Hv)).
      reflexivity.
Defined.

(* the forest's items are its blocks flattened, so a block member is a forest member *)
Lemma forest_concat_mem {p} {input : Input p} (forest : WorkForest input) :
  forall w, In w (concat (forest_blocks forest)) -> In w (forest_items forest).
Proof. intros w Hw. rewrite (forest_flat forest). exact Hw. Qed.

(** each annotated member's diagnostic is read totally off the outcome table at the member's own key *)
Definition forest_awork_diags {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (aw : WorkMember forest * list (Index.ExprRef p))
  : list (DiagnosticReason p) :=
  match total_forest_outcome_at ot (fst aw) with
  | ConversionFailure er2 tr2 opr2 t ci => [ InvalidConversion er2 tr2 opr2 (snd aw) t ci ]
  | ExpressionSuccess f =>
      match work_default_failure (work_occurrence (proj1_sig (fst aw))) f with
      | Some (c, dt) => [ DefaultNotRepresentable (work_expr_ref (proj1_sig (fst aw))) c dt ]
      | None => []
      end
  | ChildFailure => []
  end.

Lemma forest_awork_diags_eq {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) (c : list (Index.ExprRef p)) :
  forest_awork_diags ot (wm, c)
  = occurrence_expr_diags (index input) c (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)).
Proof.
  rewrite (occurrence_expr_diags_of_ref (index input) c (work_node_ref (proj1_sig wm)) (work_occurrence (proj1_sig wm))
             (work_expr_ref (proj1_sig wm)) (work_expr (proj1_sig wm))
             (work_as_expr_exact (proj1_sig wm)) (work_view_exact (proj1_sig wm))).
  unfold forest_awork_diags. cbn [fst snd].
  pose proof (total_forest_outcome_at_matches ot wm) as Hm.
  destruct (total_forest_outcome_at ot wm) as [f|er2 tr2 opr2 t ci| ]; cbn [outcome_matches] in Hm.
  - assert (Hcf : constant_info (work_expr (proj1_sig wm)) = Some (const_status f)).
    { unfold occurrence_expr_fact in Hm. rewrite (work_view_exact (proj1_sig wm)) in Hm.
      destruct (constant_info (work_expr (proj1_sig wm))) as [ce|] eqn:Ece; [| discriminate Hm].
      injection Hm as Hf0. rewrite <- Hf0. reflexivity. }
    rewrite (local_conv_failure_none_of_const (work_expr (proj1_sig wm)) (const_status f) Hcf).
    rewrite (work_default_failure_eq (work_occurrence (proj1_sig wm)) (work_expr (proj1_sig wm)) f Hcf). reflexivity.
  - destruct Hm as [_ [Hae2 [[e' [Hv' Hlcf]] [Htr2 Hopr2]]]].
    rewrite (work_as_expr_exact (proj1_sig wm)) in Hae2. injection Hae2 as He2. subst er2.
    rewrite (work_view_exact (proj1_sig wm)) in Hv'. injection Hv' as He'. subst e'.
    rewrite Hlcf, Htr2, Hopr2. reflexivity.
  - destruct Hm as [Hnf [e' [Hv' Hlcf]]]. rewrite (work_view_exact (proj1_sig wm)) in Hv'.
    injection Hv' as He'. subst e'.
    rewrite Hlcf. unfold arg_default_failure.
    assert (Hcn : constant_info (work_expr (proj1_sig wm)) = None).
    { unfold occurrence_expr_fact in Hnf. rewrite (work_view_exact (proj1_sig wm)) in Hnf.
      destruct (constant_info (work_expr (proj1_sig wm))) as [ce|] eqn:Ece; [discriminate Hnf | reflexivity]. }
    destruct (Index.occurrence_role (work_occurrence (proj1_sig wm))); try reflexivity. rewrite Hcn. reflexivity.
Qed.

(* a named projection, so the mapped form is identical across the object and the lemmas that reference it *)
Definition work_pair_ctx {p} {input : Input p} {forest : WorkForest input}
    (x : WorkMember forest * list (Index.ExprRef p))
  : (Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p) :=
  ((work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))), snd x).

(* flat_map of a singleton-valued function is a map. *)
Lemma flat_map_sing {A B} (f : A -> B) (l : list A) :
  flat_map (fun x => [f x]) l = map f l.
Proof. induction l as [|a l IH]; [reflexivity | cbn [flat_map map]; rewrite IH; reflexivity]. Qed.

(* a guarded singleton flat_map over occurrence/context pairs is the filter on the pair's occurrence. *)
Lemma flat_map_occ_is_expr_filter {p}
    (l : list ((Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p))) :
  flat_map (fun rc => if occurrence_is_expr (fst rc) then [ (fst rc, snd rc) ] else []) l
  = filter (fun rc => occurrence_is_expr (fst rc)) l.
Proof.
  induction l as [|[ro c] l IH]; [reflexivity|].
  cbn [flat_map filter fst snd]. destruct (occurrence_is_expr ro); cbn [app]; rewrite IH; reflexivity.
Qed.

(** the one retained annotated forest object, its members exactly the forest's items in forest order *)
Record AnnotatedWork {p} {input : Input p} (forest : WorkForest input) : Type :=
  MakeAnnotatedWork {
  annotated_items : list (WorkMember forest * list (Index.ExprRef p)) ;
  annotated_members : map (fun x => proj1_sig (fst x)) annotated_items = forest_items forest ;
  annotated_diag_fold :
    forall (X : Type) (d : (WorkMember forest * list (Index.ExprRef p)) -> list X)
           (dr : (Index.Snapshot.NodeRef p * Index.Occurrence) -> list (Index.ExprRef p) -> list X),
      (forall wm c, d (wm, c) = dr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)) c) ->
      (forall ro c, In ro (concat (input_blocks input)) -> Index.view_expr (snd ro) = None -> dr ro c = []) ->
      flat_map d annotated_items
      = flat_map (fun rc => dr (fst rc) (snd rc)) (annotate_program (index input)) ;
  annotated_context_sound : forall x er, In x annotated_items -> In er (snd x) ->
    is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = true
    /\ Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref er))
              (Index.Snapshot.node_ref_local (work_node_ref (proj1_sig (fst x))))
    /\ Pos.le (Index.Snapshot.node_ref_local (work_node_ref (proj1_sig (fst x))))
              (Index.Snapshot.node_subtree_end (index input) (Index.erase_ref er)) ;
  annotated_context_same_file : forall x, In x annotated_items ->
    Forall (fun er => Index.Snapshot.node_ref_file (Index.erase_ref er)
                      = Index.Snapshot.node_ref_file (work_node_ref (proj1_sig (fst x)))) (snd x) ;
  annotated_context_nearest_first : forall x, In x annotated_items ->
    StronglySorted (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b))
                                       (Index.Snapshot.node_ref_local (Index.erase_ref a))) (snd x) ;
  annotated_context_nodup : forall x, In x annotated_items -> NoDup (snd x)
}.
Arguments MakeAnnotatedWork {p input forest} _ _ _ _ _ _ _.
Arguments annotated_items {p input forest} _.  Arguments annotated_members {p input forest} _.
Arguments annotated_diag_fold {p input forest} _.  Arguments annotated_context_sound {p input forest} _.
Arguments annotated_context_same_file {p input forest} _.  Arguments annotated_context_nearest_first {p input forest} _.
Arguments annotated_context_nodup {p input forest} _.

(* the zip-fold is destructed once and its proof stored into the record's fields *)
Definition build_annotated_work_forest {p} {input : Input p} (forest : WorkForest input)
  : AnnotatedWork forest.
Proof.
  destruct (build_forest_awork_blocks forest (input_blocks input) (forest_blocks forest)
              (forest_blocks_exact forest) (forest_concat_mem forest)) as [aw [Hmem Hfoldb]].
  assert (Hprog : forall (X : Type) (d : (WorkMember forest * list (Index.ExprRef p)) -> list X)
           (dr : (Index.Snapshot.NodeRef p * Index.Occurrence) -> list (Index.ExprRef p) -> list X),
      (forall wm c, d (wm, c) = dr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)) c) ->
      (forall ro c, In ro (concat (input_blocks input)) -> Index.view_expr (snd ro) = None -> dr ro c = []) ->
      flat_map d aw = flat_map (fun rc => dr (fst rc) (snd rc)) (annotate_program (index input))).
  { intros X d dr Hag Hemp. rewrite (Hfoldb X d dr Hag Hemp).
    unfold annotate_program. rewrite (input_blocks_ok input). reflexivity. }
  assert (Hag : forall (wm : WorkMember forest) (c : list (Index.ExprRef p)),
      [ ((work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)), c) ]
      = (if occurrence_is_expr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm))
         then [ ((work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)), c) ] else [])).
  { intros wm c. rewrite (occurrence_is_expr_true (work_node_ref (proj1_sig wm)) (work_occurrence (proj1_sig wm))
        (work_expr (proj1_sig wm)) (work_view_exact (proj1_sig wm))). reflexivity. }
  assert (Hemp : forall (ro : Index.Snapshot.NodeRef p * Index.Occurrence) (c : list (Index.ExprRef p)),
      In ro (concat (input_blocks input)) -> Index.view_expr (snd ro) = None ->
      (if occurrence_is_expr ro then [ (ro, c) ] else []) = nil).
  { intros [r occ] c _ Hv. cbn [snd] in Hv. rewrite (occurrence_is_expr_false r occ Hv). reflexivity. }
  assert (Halign : map work_pair_ctx aw
                   = filter (fun rc => occurrence_is_expr (fst rc)) (annotate_program (index input))).
  { rewrite <- (flat_map_sing work_pair_ctx aw).
    rewrite (Hprog (((Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p))%type)
               (fun x => [ work_pair_ctx x ])
               (fun ro c => if occurrence_is_expr ro then [ (ro, c) ] else []) Hag Hemp).
    cbn beta. exact (flat_map_occ_is_expr_filter (annotate_program (index input))). }
  assert (Hin : forall x, In x aw ->
     In ((work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))), snd x)
        (annotate_program (index input))).
  { intros x Hx.
    assert (Hxm : In (work_pair_ctx x) (map work_pair_ctx aw)) by (apply in_map; exact Hx).
    rewrite Halign in Hxm. apply filter_In in Hxm. exact (proj1 Hxm). }
  refine (MakeAnnotatedWork aw _ Hprog _ _ _ _).
  - exact (eq_trans Hmem (eq_sym (forest_flat forest))).
  - intros x er Hx Her.
    exact (annotate_program_ctx_sound (index input)
             (work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))) (snd x) er (Hin x Hx) Her).
  - intros x Hx.
    exact (proj1 (annotate_program_ctx_wf (index input)
             (work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))) (snd x) (Hin x Hx))).
  - intros x Hx.
    exact (proj1 (proj2 (annotate_program_ctx_wf (index input)
             (work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))) (snd x) (Hin x Hx)))).
  - intros x Hx.
    exact (proj2 (proj2 (annotate_program_ctx_wf (index input)
             (work_node_ref (proj1_sig (fst x)), work_occurrence (proj1_sig (fst x))) (snd x) (Hin x Hx)))).
Qed.

(* the alignment is derived from the object's own carried fold, never from a rebuild *)
Lemma annotated_align_eq {p} {input : Input p} {forest : WorkForest input}
    (aw : AnnotatedWork forest) :
  map work_pair_ctx (annotated_items aw)
  = filter (fun rc => occurrence_is_expr (fst rc)) (annotate_program (index input)).
Proof.
  assert (Hag : forall (wm : WorkMember forest) (c : list (Index.ExprRef p)),
      [ ((work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)), c) ]
      = (if occurrence_is_expr (work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm))
         then [ ((work_node_ref (proj1_sig wm), work_occurrence (proj1_sig wm)), c) ] else [])).
  { intros wm c. rewrite (occurrence_is_expr_true (work_node_ref (proj1_sig wm)) (work_occurrence (proj1_sig wm))
        (work_expr (proj1_sig wm)) (work_view_exact (proj1_sig wm))). reflexivity. }
  assert (Hemp : forall (ro : Index.Snapshot.NodeRef p * Index.Occurrence) (c : list (Index.ExprRef p)),
      In ro (concat (input_blocks input)) -> Index.view_expr (snd ro) = None ->
      (if occurrence_is_expr ro then [ (ro, c) ] else []) = nil).
  { intros [r occ] c _ Hv. cbn [snd] in Hv. rewrite (occurrence_is_expr_false r occ Hv). reflexivity. }
  rewrite <- (flat_map_sing work_pair_ctx (annotated_items aw)).
  rewrite (annotated_diag_fold aw (((Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p))%type)
             (fun x => [ work_pair_ctx x ])
             (fun ro c => if occurrence_is_expr ro then [ (ro, c) ] else []) Hag Hemp).
  cbn beta. exact (flat_map_occ_is_expr_filter (annotate_program (index input))).
Qed.

(* the diagnostic projection equals the specification, proved from the object's own fold *)
Lemma expression_diagnostics_eq_spec {p} {input : Input p} {forest : WorkForest input}
    {tnft : TypeNameFacts p} (ot : Outcomes forest tnft) (aw : AnnotatedWork forest) :
  flat_map (forest_awork_diags ot) (annotated_items aw)
  = flat_map (fun roc => occurrence_expr_diags (index input) (snd roc) (fst roc)) (annotate_program (index input)).
Proof.
  apply (annotated_diag_fold aw (DiagnosticReason p)
           (forest_awork_diags ot) (fun ro c => occurrence_expr_diags (index input) c ro)).
  - intros wm c. exact (forest_awork_diags_eq ot wm c).
  - intros ro c _ Hv. exact (occurrence_expr_diags_nonexpr (index input) c ro Hv).
Qed.

(** the fact table object carries the proof its map is the projection, indexed by the forest and table *)
Record ExpressionFacts {p} {input : Input p} (forest : WorkForest input)
    {tnft : TypeNameFacts p} (ot : Outcomes forest tnft) : Type := MakeExpressionFacts {
  expression_facts_table   : ExpressionFactTable p (indexed input) ;
  expression_facts_is_facts : fact_table_map expression_facts_table = forest_facts forest tnft ot
}.
Arguments MakeExpressionFacts {p input forest tnft ot} _ _.
Arguments expression_facts_table {p input forest tnft ot} _.  Arguments expression_facts_is_facts {p input forest tnft ot} _.

Definition build_forest_expr_fact_table {p} {input : Input p} (forest : WorkForest input)
    {tnft : TypeNameFacts p} (ot : Outcomes forest tnft) : ExpressionFacts forest ot.
Proof.
  refine (MakeExpressionFacts (MakeExpressionFactTable (forest_facts forest tnft ot) _ _) eq_refl).
  - intros k f Hf. rewrite (forest_facts_eq_spec forest tnft ot) in Hf.
    exact (program_expr_facts_domain p k f Hf).
  - intros r occ Hin. rewrite (forest_facts_eq_spec forest tnft ot).
    exact (program_expr_facts_find p r occ Hin).
Defined.

(** the diagnostics object carries the proof its list is the projection, indexed by the objects it reads *)
Record Diagnostics {p} {input : Input p} {forest : WorkForest input}
    (aw : AnnotatedWork forest)
    {tnft : TypeNameFacts p} (ot : Outcomes forest tnft) : Type := MakeDiagnostics {
  erased_diagnostics    : list (DiagnosticReason p) ;
  erased_is_diagnostics : erased_diagnostics = flat_map (forest_awork_diags ot) (annotated_items aw)
}.
Arguments MakeDiagnostics {p input forest aw tnft ot} _ _.
Arguments erased_diagnostics {p input forest aw tnft ot} _.  Arguments erased_is_diagnostics {p input forest aw tnft ot} _.

Definition build_expression_diagnostics {p} {input : Input p} {forest : WorkForest input}
    (aw : AnnotatedWork forest)
    {tnft : TypeNameFacts p} (ot : Outcomes forest tnft) : Diagnostics aw ot :=
  MakeDiagnostics (flat_map (forest_awork_diags ot) (annotated_items aw)) eq_refl.

(** the one expression phase, a dependent chain in which each component is typed by the object before it *)
Record Phase {p} (input : Input p) : Type := MakePhase {
  phase_work  : WorkForest input ;
  phase_type_name_facts  : TypeNameFacts p ;
  phase_ot    : Outcomes phase_work phase_type_name_facts ;
  phase_awork : AnnotatedWork phase_work ;
  phase_fact_table   : ExpressionFacts phase_work phase_ot ;
  phase_diag  : Diagnostics phase_awork phase_ot
}.
Arguments MakePhase {p input} _ _ _ _ _ _.
Arguments phase_work {p input} _.  Arguments phase_type_name_facts {p input} _.  Arguments phase_ot {p input} _.
Arguments phase_awork {p input} _.  Arguments phase_fact_table {p input} _.  Arguments phase_diag {p input} _.

Definition build_expression_phase {p} (input : Input p) : Phase input :=
  let work  := build_expr_work_forest input in
  let tnft  := build_type_name_fact_table input in
  let ot    := build_forest_outcome_table work tnft in
  let awork := build_annotated_work_forest work in
  let eft   := build_forest_expr_fact_table work ot in
  let diag  := build_expression_diagnostics awork ot in
  MakePhase work tnft ot awork eft diag.

(** each phase component is the builder applied to the phase's own prior objects, definitionally *)
Lemma phase_ot_consumes_work {p} (input : Input p) :
  phase_ot (build_expression_phase input)
  = build_forest_outcome_table (phase_work (build_expression_phase input)) (phase_type_name_facts (build_expression_phase input)).
Proof. reflexivity. Qed.
Lemma phase_awork_consumes_work {p} (input : Input p) :
  phase_awork (build_expression_phase input) = build_annotated_work_forest (phase_work (build_expression_phase input)).
Proof. reflexivity. Qed.
Lemma phase_fact_table_consumes_work_outcomes {p} (input : Input p) :
  phase_fact_table (build_expression_phase input)
  = build_forest_expr_fact_table (phase_work (build_expression_phase input)) (phase_ot (build_expression_phase input)).
Proof. reflexivity. Qed.
Lemma phase_diag_consumes_awork_ot {p} (input : Input p) :
  phase_diag (build_expression_phase input)
  = build_expression_diagnostics (phase_awork (build_expression_phase input)) (phase_ot (build_expression_phase input)).
Proof. reflexivity. Qed.

(* the phase's fact projection is the retained table's map, never a recomputed value *)
Definition phase_facts {p} {input : Input p} (ph : Phase input)
  : Index.KeyMap.t ExpressionFact := fact_table_map (expression_facts_table (phase_fact_table ph)).
(* the phase's STORED diagnostic list IS the retained [phase_diag] object's list. *)
Definition phase_diags {p} {input : Input p} (ph : Phase input)
  : list (DiagnosticReason p) := erased_diagnostics (phase_diag ph).

(* the total query depends only on the member's key *)
Lemma total_forest_outcome_at_congr {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (w1 w2 : WorkMember forest) :
  proj1_sig w1 = proj1_sig w2 -> total_forest_outcome_at ot w1 = total_forest_outcome_at ot w2.
Proof. intro Heq. unfold total_forest_outcome_at. apply from_some_congr. rewrite Heq. reflexivity. Qed.

(* §5 the retained trace's insertion sequence — the [current] of each [TraceStep], collected top-down. *)
Fixpoint trace_currents {p} {input : Input p} {forest : WorkForest input} {tnft}
    {items : list (Work input)} {acc : Accumulator forest tnft items}
    (t : Trace forest tnft items acc) : list (Work input) :=
  match t with
  | EmptyTrace => []
  | TraceStep current _ _ _ _ _ tail _ => current :: trace_currents tail
  end.
Lemma trace_currents_eq {p} {input : Input p} {forest : WorkForest input} {tnft} :
  forall items acc (t : Trace forest tnft items acc), trace_currents t = items.
Proof.
  intros items acc t. induction t as [ | current rest acc_rest o Hin Hfresh tail IH sc ]; [reflexivity |].
  cbn [trace_currents]. rewrite IH. reflexivity.
Qed.

(* every retained member is inserted by exactly one trace step, and no two steps share a key *)
Lemma outcome_trace_unique_step {p} {input : Input p} {forest : WorkForest input} {tnft}
    (acc : Accumulator forest tnft (forest_items forest))
    (t : Trace forest tnft (forest_items forest) acc) :
  trace_currents t = forest_items forest
  /\ NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w)) (trace_currents t)).
Proof.
  split.
  - exact (trace_currents_eq (forest_items forest) acc t).
  - rewrite (trace_currents_eq (forest_items forest) acc t). exact (forest_keys_nodup forest).
Qed.

(** the accepted conversion cause is stated over the retained cause object, not over a chosen suffix *)
Definition accepted_conversion_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Prop :=
  let cause    := total_forest_outcome_cause ot wm in
  let rest     := projT1 cause in
  let acc_rest := projT1 (projT2 cause) in
     work_expr (proj1_sig wm) = Syntax.Convert ts x
  (* the exact suffix split the cause retained — this member sits exactly before that exact tail *)
  /\ (exists prefix, forest_items forest = prefix ++ proj1_sig wm :: rest)
  /\ exists (step : ConversionStep forest (proj1_sig wm) rest ts x) opf f tc,
       (* this member's FINAL outcome … *)
       total_forest_outcome_at ot wm = ExpressionSuccess f
       (* … the operand's outcome read through the RETAINED tail accumulator at its exact SuffixMember … *)
    /\ accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step)) = ExpressionSuccess opf
       (* … the tail-to-final preservation at that exact operand member … *)
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step))
       = accumulator_total acc_rest (step_operand_suffix step)
       (* … the ONE [Typing.convert_constant] on the exact target type-name fact … *)
    /\ Typing.convert_constant
         (fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step))))
         (const_status opf) = Some tc
       (* … the operand [Index.ExprRef] the conversion CARRIES — not a separately guessed source value … *)
    /\ conversion_operand_ref (index input) (work_expr_ref (proj1_sig wm))
       = Some (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
       (* … which the RETAINED index answers with that EXACT retained operand member … *)
    /\ Index.KeyMap.find
         (Index.Snapshot.node_ref_key
            (Index.erase_ref (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))))
         (index_map (forest_index forest))
       = Some (proj1_sig (conversion_operand_work (step_conversion step)))
       (* … that member IS the step's operand [SuffixMember], and it lies in the cause's own processed suffix … *)
    /\ proj1_sig (proj1_sig (step_operand_suffix step))
       = proj1_sig (conversion_operand_work (step_conversion step))
    /\ In (proj1_sig (conversion_operand_work (step_conversion step))) rest
       (* … and [f] IS the exact current [ExpressionFact]. *)
    /\ f = MakeExpressionFact
             (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft
                (conversion_target_node_ref (step_conversion step)))) tc)
             (use_resolved_of_input (expression_ref_role (work_expr_ref (proj1_sig wm)))
                (Typing.TypedInfo (fact_type (type_name_fact_at_table tnft
                   (conversion_target_node_ref (step_conversion step)))) tc)).

(* the cause-owned form destructs the one retained cause and introduces no second accumulator *)
Lemma retained_convsuccess_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) ts x f :
  work_expr (proj1_sig wm) = Syntax.Convert ts x ->
  total_forest_outcome_at ot wm = ExpressionSuccess f ->
  accepted_conversion_cause ot wm ts x.
Proof.
  intros He Hok. unfold accepted_conversion_cause. cbv zeta.
  destruct (total_forest_outcome_cause ot wm) as [rest [acc_rest [[Hsplit stepc] Hpreserve]]].
  cbn [projT1 projT2].
  split; [ exact He | split; [ exact Hsplit | ] ].
  (* the two spellings are convertible but not syntactically equal, and rewriting is syntactic *)
  assert (Hok' : accumulator_total (outcomes_acc ot) (wm_suffix wm) = ExpressionSuccess f) by exact Hok.
  rewrite Hok' in stepc.
  destruct (conversion_success_cause_yields_step _ rest acc_rest ts x f He stepc)
    as [step [opf [tc [Hopf [Hconv Hf]]]]].
  pose proof (final_operand_outcome ot rest acc_rest Hpreserve (step_operand_suffix step)) as Hcl.
  exists step, opf, f, tc.
  split; [ exact Hok | ].
  split; [ exact Hopf | ].
  split; [ rewrite Hcl; exact Hopf | ].
  split; [ exact Hcl | ].
  split; [ exact Hconv | ].
  (* the operand navigation, over the SAME [step] the cause supplied *)
  split; [ exact (conversion_operand_ref_eq (step_conversion step)) | ].
  split.
  { rewrite (work_erase_exact (proj1_sig (conversion_operand_work (step_conversion step)))).
    exact (proj2 (index_exact (forest_index forest)
                    _ (proj1_sig (conversion_operand_work (step_conversion step))))
                 (conj (proj2_sig (conversion_operand_work (step_conversion step))) eq_refl)). }
  split; [ exact (step_operand_exact step) | ].
  split.
  { rewrite <- (step_operand_exact step). exact (proj2_sig (step_operand_suffix step)). }
  exact Hf.
Qed.

(** the rejected counterparts, over the same retained cause object rather than a freely chosen one *)
Definition rejected_conversion_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) (ts : Syntax.TypeExpr) (x : Syntax.Expr)
    (* a continuation keeps a fixture's extra facts inside the step's own existential scope *)
    (extra : ConversionStep forest (proj1_sig wm) (projT1 (total_forest_outcome_cause ot wm)) ts x
             -> ExpressionFact -> Typing.SemanticType -> Prop) : Prop :=
  let cause    := total_forest_outcome_cause ot wm in
  let rest     := projT1 cause in
  let acc_rest := projT1 (projT2 cause) in
     work_expr (proj1_sig wm) = Syntax.Convert ts x
  /\ (exists prefix, forest_items forest = prefix ++ proj1_sig wm :: rest)
  /\ exists (step : ConversionStep forest (proj1_sig wm) rest ts x) opf t,
       (* the final outcome names this member's own reference and the step's own target and operand *)
       total_forest_outcome_at ot wm
         = ConversionFailure (work_expr_ref (proj1_sig wm)) (conversion_target_node_ref (step_conversion step))
             (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step)))) t (const_status opf)
       (* the operand SUCCEEDED, read through the RETAINED tail accumulator, and that outcome is preserved *)
    /\ accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step)) = ExpressionSuccess opf
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step))
       = accumulator_total acc_rest (step_operand_suffix step)
       (* the ONE [Typing.convert_constant], and it REJECTED *)
    /\ Typing.convert_constant t (const_status opf) = None
       (* the resolved target type IS the exact predeclared-context table query for that ref *)
    /\ t = fact_type (type_name_fact_at_table tnft (conversion_target_node_ref (step_conversion step)))
       (* … and whatever the concrete fixture must say about THIS step *)
    /\ extra step opf t.

Lemma retained_convfail_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) ts x er tr opr t ci extra :
  work_expr (proj1_sig wm) = Syntax.Convert ts x ->
  total_forest_outcome_at ot wm = ConversionFailure er tr opr t ci ->
  (* the caller proves its [extra] for the step the cause supplies, with the cause's own facts in hand *)
  (forall (step : ConversionStep forest (proj1_sig wm) (projT1 (total_forest_outcome_cause ot wm)) ts x) opf,
     work_expr (proj1_sig wm) = Syntax.Convert ts x ->
     total_forest_outcome_at ot wm
       = ConversionFailure (work_expr_ref (proj1_sig wm)) (conversion_target_node_ref (step_conversion step))
           (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step)))) t (const_status opf) ->
     extra step opf t) ->
  rejected_conversion_cause ot wm ts x extra.
Proof.
  intros He Hcv Hextra. unfold rejected_conversion_cause. cbv zeta.
  destruct (total_forest_outcome_cause ot wm) as [rest [acc_rest [[Hsplit stepc] Hpreserve]]].
  cbn [projT1 projT2].
  split; [ exact He | split; [ exact Hsplit | ] ].
  (* same convertibility note as the success side: restate the outcome in the cause's own spelling. *)
  assert (Hidx : accumulator_total (outcomes_acc ot) (wm_suffix wm) = ConversionFailure er tr opr t ci)
    by exact Hcv.
  (* the cause is rebuilt rather than rewritten, because the extra facts mention it *)
  assert (stepc' : StepCause forest tnft (proj1_sig wm) rest acc_rest (ConversionFailure er tr opr t ci))
    by (rewrite <- Hidx; exact stepc).
  destruct (conversion_failure_cause_yields_step _ rest acc_rest er tr opr t ci stepc')
    as [ts0 [x0 [step [opf [Hstep_e [Hopf [Her [Htr [Hopr [Ht [Hci Hconv]]]]]]]]]]].
  assert (Heq : Syntax.Convert ts0 x0 = Syntax.Convert ts x) by (rewrite <- Hstep_e; exact He).
  injection Heq as Hts0 Hx0. subst ts0 x0.
  pose proof (final_operand_outcome ot rest acc_rest Hpreserve (step_operand_suffix step)) as Hcl.
  assert (Hout : total_forest_outcome_at ot wm
                 = ConversionFailure (work_expr_ref (proj1_sig wm))
                     (conversion_target_node_ref (step_conversion step))
                     (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                     t (const_status opf))
    by (rewrite Hcv, Her, Htr, Hopr, Hci; reflexivity).
  assert (Hfin : total_forest_outcome_at ot (proj1_sig (step_operand_suffix step)) = ExpressionSuccess opf)
    by (rewrite Hcl; exact Hopf).
  (* the rejecting query is stated over the operand fact's status, not over a loosely named one *)
  rewrite Hci in Hconv.
  exists step, opf, t.
  exact (conj Hout (conj Hopf (conj Hfin (conj Hcl (conj Hconv (conj Ht (Hextra step opf He Hout))))))).
Qed.

(** an enclosing conversion whose own outcome is a child failure, again over the cause's own suffix *)
Definition childfail_conversion_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Prop :=
  let cause    := total_forest_outcome_cause ot wm in
  let rest     := projT1 cause in
  let acc_rest := projT1 (projT2 cause) in
     work_expr (proj1_sig wm) = Syntax.Convert ts x
  /\ total_forest_outcome_at ot wm = ChildFailure
  /\ (exists prefix, forest_items forest = prefix ++ proj1_sig wm :: rest)
  /\ exists step : ConversionStep forest (proj1_sig wm) rest ts x,
       outcome_is_fail (accumulator_total acc_rest (step_operand_suffix step))
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step))
       = accumulator_total acc_rest (step_operand_suffix step)
    /\ outcome_is_fail (total_forest_outcome_at ot (proj1_sig (step_operand_suffix step)))
       (* an enclosing failure contributes NO diagnostic of its own, whatever annotation context it carries *)
    /\ (forall c, forest_awork_diags ot (wm, c) = []).

Lemma retained_childfail_cause {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (wm : WorkMember forest) ts x :
  work_expr (proj1_sig wm) = Syntax.Convert ts x ->
  total_forest_outcome_at ot wm = ChildFailure ->
  childfail_conversion_cause ot wm ts x.
Proof.
  intros He Hcf. unfold childfail_conversion_cause. cbv zeta.
  destruct (total_forest_outcome_cause ot wm) as [rest [acc_rest [[Hsplit stepc] Hpreserve]]].
  cbn [projT1 projT2].
  split; [ exact He | split; [ exact Hcf | split; [ exact Hsplit | ] ] ].
  assert (Hidx : accumulator_total (outcomes_acc ot) (wm_suffix wm) = ChildFailure) by exact Hcf.
  rewrite Hidx in stepc.
  destruct (child_failure_cause_yields_member _ rest acc_rest stepc) as [ts0 [x0 [step [Hstep_e Hfail]]]].
  assert (Heq : Syntax.Convert ts0 x0 = Syntax.Convert ts x) by (rewrite <- Hstep_e; exact He).
  injection Heq as Hts0 Hx0. subst ts0 x0.
  pose proof (final_operand_outcome ot rest acc_rest Hpreserve (step_operand_suffix step)) as Hcl.
  assert (Hfinfail : outcome_is_fail (total_forest_outcome_at ot (proj1_sig (step_operand_suffix step))))
    by (rewrite Hcl; exact Hfail).
  assert (Hnodiag : forall c, forest_awork_diags ot (wm, c) = [])
    by (intro c; unfold forest_awork_diags; cbn [fst snd]; rewrite Hcf; reflexivity).
  exists step.
  exact (conj Hfail (conj Hcl (conj Hfinfail Hnodiag))).
Qed.

(* the stored diagnostic reads the stored outcome directly, over the member's own retained context *)
Lemma retained_convfail_diag {p} {input : Input p} {forest : WorkForest input} {tnft}
    (ot : Outcomes forest tnft) (aw : AnnotatedWork forest) (wm : WorkMember forest)
    er tr opr t ci :
  total_forest_outcome_at ot wm = ConversionFailure er tr opr t ci ->
  exists (wma : WorkMember forest) (outer : list (Index.ExprRef p)),
       In (wma, outer) (annotated_items aw)
    /\ proj1_sig wma = proj1_sig wm
    /\ In (InvalidConversion er tr opr outer t ci) (flat_map (forest_awork_diags ot) (annotated_items aw)).
Proof.
  intro Hcv.
  assert (Hin : In (proj1_sig wm) (map (fun x => proj1_sig (fst x)) (annotated_items aw))).
  { rewrite (annotated_members aw). exact (proj2_sig wm). }
  apply in_map_iff in Hin. destruct Hin as [x [Hx Hinx]].
  destruct x as [wmx cx]. cbn [fst snd] in Hx.
  exists wmx, cx.
  assert (Hfx : total_forest_outcome_at ot wmx = ConversionFailure er tr opr t ci).
  { transitivity (total_forest_outcome_at ot wm);
      [ exact (total_forest_outcome_at_congr ot wmx wm Hx) | exact Hcv ]. }
  assert (Hdiag : forest_awork_diags ot (wmx, cx) = [InvalidConversion er tr opr cx t ci]).
  { unfold forest_awork_diags. cbn [fst snd]. rewrite Hfx. reflexivity. }
  split; [ exact Hinx | split; [ exact Hx | ] ].
  apply in_flat_map. exists (wmx, cx). split; [ exact Hinx | rewrite Hdiag; left; reflexivity ].
Qed.

(* a diagnostic list of length one containing an element IS that singleton. *)
Lemma length_one_in_eq {A} (l : list A) (x : A) : length l = 1%nat -> In x l -> l = [x].
Proof.
  intros Hlen Hin. destruct l as [|a [|b l']]; try discriminate Hlen.
  destruct Hin as [Hax | []]. rewrite Hax. reflexivity.
Qed.

(** the sealed facts and the stored diagnostics are both typed by the same retained outcome table *)
Theorem facts_and_diags_share_phase {p} (input : Input p) (ph : Phase input) :
  phase_facts ph = program_expr_facts p
  /\ phase_diags ph = flat_map (fun roc => occurrence_expr_diags (index input) (snd roc) (fst roc)) (annotate_program (index input)).
Proof.
  split.
  - unfold phase_facts. rewrite (expression_facts_is_facts (phase_fact_table ph)).
    exact (forest_facts_eq_spec (phase_work ph) (phase_type_name_facts ph) (phase_ot ph)).
  - unfold phase_diags. rewrite (erased_is_diagnostics (phase_diag ph)).
    exact (expression_diagnostics_eq_spec (phase_ot ph) (phase_awork ph)).
Qed.

(* the phase diagnostics EQUAL the spec [expression_diags] (for the decision infrastructure). *)
Lemma phase_diags_eq_expr_diags {p} (input : Input p) (ph : Phase input) :
  phase_diags ph = expression_diags (index input).
Proof. rewrite (proj2 (facts_and_diags_share_phase input ph)), (expression_diags_eq_spec (index input)). reflexivity. Qed.

(** every enclosing context in the whole report is a genuine strict-ancestor conversion *)
Lemma expression_diags_conversion_single_rounding_sound {p} (idx : Index.Snapshot.Syntax p) er tr opr outer t ci :
  In (InvalidConversion er tr opr outer t ci) (expression_diags idx) ->
  forall a, In a outer ->
    is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref a)) = true
    /\ Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref a)) (Index.Snapshot.node_ref_local (Index.erase_ref er))
    /\ Pos.le (Index.Snapshot.node_ref_local (Index.erase_ref er)) (Index.Snapshot.node_subtree_end idx (Index.erase_ref a)).
Proof.
  intros Hin a Ha. rewrite expression_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occurrence_expr_diags_conv_sound idx (fst roc) (snd roc) er tr opr outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_sound idx (fst roc) (snd roc) a Hroc2 Ha) as [Hconv [Hlt Hle]].
  assert (Her : Index.erase_ref er = fst (fst roc))
    by exact (Index.erase_as_kind idx (fst (fst roc)) Index.ExpressionKind er Hae).
  rewrite Her. split; [exact Hconv | split; [exact Hlt | exact Hle]].
Qed.

(** the whole report's enclosing contexts are same-file, nearest-first and duplicate-free *)
Lemma expression_diags_conversion_single_rounding_well_formed {p} (idx : Index.Snapshot.Syntax p) er tr opr outer t ci :
  In (InvalidConversion er tr opr outer t ci) (expression_diags idx) ->
  Forall (fun a => Index.Snapshot.node_ref_file (Index.erase_ref a) = Index.Snapshot.node_ref_file (Index.erase_ref er)) outer
  /\ StronglySorted (fun a b => Pos.lt (Index.Snapshot.node_ref_local (Index.erase_ref b)) (Index.Snapshot.node_ref_local (Index.erase_ref a))) outer
  /\ NoDup outer.
Proof.
  intro Hin. rewrite expression_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occurrence_expr_diags_conv_sound idx (fst roc) (snd roc) er tr opr outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_wf idx (fst roc) (snd roc) Hroc2) as [Hfile [Hss Hnd]].
  assert (Her : Index.erase_ref er = fst (fst roc))
    by exact (Index.erase_as_kind idx (fst (fst roc)) Index.ExpressionKind er Hae).
  rewrite Her. split; [exact Hfile | split; [exact Hss | exact Hnd]].
Qed.

(** the index-free predicate for an occurrence that emits nothing *)
Definition occurrence_local_ok (occ : Index.Occurrence) : bool :=
  match Index.view_expr occ with
  | Some e => match local_conv_failure e with Some _ => false | None => true end
  | None => true
  end.
Definition occurrence_default_ok (occ : Index.Occurrence) : bool :=
  match Index.view_expr occ with
  | Some e => match arg_default_failure occ e with Some _ => false | None => true end
  | None => true
  end.
Definition occurrence_emits_none_pure (occ : Index.Occurrence) : bool :=
  occurrence_local_ok occ && occurrence_default_ok occ.

(* a conversion's TYPE-NAME occurrence (no expression view) is vacuously local-OK / default-OK / emit-none. *)
Lemma occurrence_local_ok_typename : forall ts par sub,
  occurrence_local_ok (Index.MakeOccurrence Index.TypeNameKind (Index.TypeNameView ts) (Some par) Index.ConversionTarget sub) = true.
Proof. reflexivity. Qed.
Lemma occurrence_default_ok_typename : forall ts par sub,
  occurrence_default_ok (Index.MakeOccurrence Index.TypeNameKind (Index.TypeNameView ts) (Some par) Index.ConversionTarget sub) = true.
Proof. reflexivity. Qed.
Lemma occurrence_emits_none_pure_typename : forall ts par sub,
  occurrence_emits_none_pure (Index.MakeOccurrence Index.TypeNameKind (Index.TypeNameView ts) (Some par) Index.ConversionTarget sub) = true.
Proof. reflexivity. Qed.

(** every use-context type is allowed for a println argument (the type universe is exactly the allowed set). *)
Lemma use_allowsb_println_true : forall t, use_allowsb Typing.PrintlnArgument t = true.
Proof. intro t; destruct t; reflexivity. Qed.

(** KEY: no conversion in a subtree locally fails IFF the subtree's [constant_info] succeeds. *)
Lemma conv_ok_fold : forall e parent role me,
  forallb (fun x => occurrence_local_ok (snd x)) (Index.occurrences_expr parent role me e)
  = match constant_info e with Some _ => true | None => false end.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent role me.
  1,2,3,4,5,6: reflexivity.
  cbn [Index.occurrences_expr forallb snd].
  rewrite occurrence_local_ok_typename.
  unfold occurrence_local_ok at 1; cbn [Index.view_expr Index.occurrence_view];
  cbn [local_conv_failure]; cbn [Typing.constant_info];
  specialize (IHx me Index.ConversionOperand (Pos.succ (Pos.succ me)));
  destruct (constant_info x) as [ci|] eqn:Ex;
  [ destruct (Typing.convert_constant _ ci) as [ci'|] eqn:Ec;
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
Lemma occurrence_default_ok_operand : forall e par sub,
  occurrence_default_ok (Index.MakeOccurrence Index.ExpressionKind (Index.ExpressionView e) (Some par) Index.ConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occurrence_default_ok_operand_true : forall e parent me,
  forallb (fun x => occurrence_default_ok (snd x)) (Index.occurrences_expr parent Index.ConversionOperand me e) = true.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent me; cbn [Index.occurrences_expr forallb snd].
  1,2,3,4,5,6: rewrite occurrence_default_ok_operand; reflexivity.
  rewrite occurrence_default_ok_operand, occurrence_default_ok_typename, !Bool.andb_true_l; apply IHx.
Qed.

(** a println-argument root occurrence is default-OK IFF its untyped constant defaults (typed / failed = OK). *)
Lemma occurrence_default_ok_printlnarg : forall e par aidx sub,
  occurrence_default_ok (Index.MakeOccurrence Index.ExpressionKind (Index.ExpressionView e) (Some par) (Index.PrintlnArgument aidx) sub)
  = match constant_info e with Some (Typing.UntypedInfo c) => match Typing.default_constant c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e par aidx sub. unfold occurrence_default_ok.
  cbn [Index.view_expr Index.occurrence_view arg_default_failure Index.occurrence_role].
  destruct (constant_info e) as [[c|t tc]|]; [ destruct (Typing.default_constant c) | | ]; reflexivity.
Qed.

Lemma occurrence_default_fold_arg : forall e parent aidx me,
  forallb (fun x => occurrence_default_ok (snd x)) (Index.occurrences_expr parent (Index.PrintlnArgument aidx) me e)
  = match constant_info e with Some (Typing.UntypedInfo c) => match Typing.default_constant c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e parent aidx me. destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [Index.occurrences_expr forallb snd].
  1,2,3,4,5,6: rewrite Bool.andb_true_r; apply occurrence_default_ok_printlnarg.
  rewrite occurrence_default_ok_typename, occurrence_default_ok_operand_true, ?Bool.andb_true_r, ?Bool.andb_true_l;
    apply occurrence_default_ok_printlnarg.
Qed.

(** ONE println argument's occurrence stream emits nothing IFF the argument resolves ([expression_typedb]). *)
Lemma occurrence_emits_arg : forall e parent aidx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_arg parent aidx me e) = expression_typedb Typing.PrintlnArgument e.
Proof.
  intros e parent aidx me. unfold Index.occurrences_arg, occurrence_emits_none_pure.
  rewrite forallb_andb, conv_ok_fold, occurrence_default_fold_arg.
  unfold Typing.expression_typedb, Typing.resolve, Typing.resolve_constant.
  destruct (constant_info e) as [[c|t tc]|]; cbn [Typing.resolve_constant_info].
  - destruct (Typing.default_constant c) as [rc|]; cbn [option_map]; [ rewrite use_allowsb_println_true |]; reflexivity.
  - cbn [option_map]. rewrite use_allowsb_println_true. reflexivity.
  - cbn [option_map]. reflexivity.
Qed.

Lemma occurrence_emits_args : forall es parent aidx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_args parent aidx me es)
  = forallb (expression_typedb Typing.PrintlnArgument) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [Index.occurrences_args]. rewrite forallb_app, occurrence_emits_arg, IH. reflexivity.
Qed.

Lemma occurrence_emits_stmt : forall s parent sidx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_stmt parent sidx me s) = stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [Index.occurrences_stmt forallb occurrence_emits_none_pure occurrence_local_ok occurrence_default_ok snd
       Index.view_expr Index.occurrence_view].
  rewrite occurrence_emits_args. reflexivity.
Qed.

Lemma occurrence_emits_stmts : forall ss parent sidx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_stmts parent sidx me ss) = forallb stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [Index.occurrences_stmts]. rewrite forallb_app, occurrence_emits_stmt, IH. reflexivity.
Qed.

Lemma occurrence_emits_decl : forall d parent didx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_decl parent didx me d) = decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [Index.occurrences_decl forallb occurrence_emits_none_pure occurrence_local_ok occurrence_default_ok snd
       Index.view_expr Index.occurrence_view].
  rewrite occurrence_emits_stmts. reflexivity.
Qed.

Lemma occurrence_emits_decls : forall ds parent didx me,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_decls parent didx me ds) = forallb decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [Index.occurrences_decls]. rewrite forallb_app, occurrence_emits_decl, IH. reflexivity.
Qed.

Lemma occurrence_emits_file : forall f,
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.occurrences_file f) = source_file_typedb f.
Proof.
  intros f. unfold Index.occurrences_file. destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  cbn [forallb occurrence_emits_none_pure occurrence_local_ok occurrence_default_ok snd Index.view_expr Index.occurrence_view].
  rewrite occurrence_emits_decls. unfold Typing.source_file_typedb, Typing.file_typedb. reflexivity.
Qed.

(** lift the file-level emit fold to the whole program (via the traversal projection). *)
Lemma visit_file_emits {p} (fr : Index.Snapshot.FileRef p) :
  forallb (fun x => occurrence_emits_none_pure (snd x)) (Index.Snapshot.visit_file fr)
  = source_file_typedb (Index.Snapshot.file_ref_source fr).
Proof.
  rewrite Typing.forallb_map_snd, Index.Snapshot.visit_file_snd, <- Typing.forallb_map_snd.
  apply occurrence_emits_file.
Qed.

Lemma emits_none_program_typedb (p : Syntax.Program) :
  forallb (fun x => occurrence_emits_none_pure (snd x)) (program_visit p) = program_typedb p.
Proof.
  rewrite program_visit_flat_map, forallb_flat_map. unfold Typing.program_typedb.
  apply Typing.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (Syntax.file_bindings_find (Syntax.files p) b Hb) as Hfind.
  destruct (Index.Snapshot.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_emits, Hsrc. reflexivity.
Qed.

(** every program-visited occurrence IS its reference's exact source occurrence. *)
Lemma program_visit_view (p : Syntax.Program) (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (program_visit p) -> occ = Index.Snapshot.source_occurrence_of_ref r.
Proof.
  rewrite program_visit_flat_map. intro Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hin]].
  unfold binding_visit in Hin. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [Hocc _]. exact Hocc.
Qed.

(** per-occurrence: the emitted diagnostics are empty IFF the occurrence emits nothing (pure). *)
Lemma occurrence_expr_diags_empty {p} (idx : Index.Snapshot.Syntax p) (outer : list (Index.ExprRef p))
    (r : Index.Snapshot.NodeRef p) occ :
  In (r, occ) (program_visit p) ->
  (occurrence_expr_diags idx outer (r, occ) = nil <-> occurrence_emits_none_pure occ = true).
Proof.
  intro Hin. pose proof (program_visit_view p r occ Hin) as Hocc.
  unfold occurrence_emits_none_pure, occurrence_local_ok, occurrence_default_ok. cbn [fst snd].
  unfold occurrence_expr_diags. cbn [fst snd].
  destruct (Index.as_expr idx r) as [er|] eqn:Ea.
  - assert (Hke : Index.occurrence_kind occ = Index.ExpressionKind).
    { rewrite Hocc, <- (Index.Snapshot.node_kind_matches_source p idx r).
      unfold Index.as_expr, Index.as_kind in Ea.
      destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx r) Index.ExpressionKind) as [Hk|]; [exact Hk|discriminate Ea]. }
    destruct (Index.kind_view_expr occ Hke) as [e Hve]. rewrite Hve.
    destruct (local_conv_failure e) as [[t ci]|] eqn:Elc; cbn [andb].
    + (* a real conversion mints its target ref, so the emitted list is a nonempty singleton *)
      destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate Elc.
      destruct (conversion_target_ref_conv idx r occ er ts x Hin Hve Ea) as [tr [Hctr _]].
      destruct (conversion_operand_ref_conv idx r occ er ts x Hin Hve Ea) as [opr [Hcor _]].
      rewrite Hctr, Hcor. split; intro H; discriminate H.
    + destruct (arg_default_failure occ e) as [[c dt]|]; cbn [andb];
        split; intro H; try discriminate H; reflexivity.
  - assert (Hve : Index.view_expr occ = None).
    { destruct (Index.view_expr occ) as [e|] eqn:E; [| reflexivity].
      exfalso. unfold Index.as_expr, Index.as_kind in Ea.
      destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx r) Index.ExpressionKind) as [|Hk]; [discriminate Ea|].
      apply Hk. rewrite (Index.Snapshot.node_kind_matches_source p idx r), <- Hocc. exact (Index.view_expr_kind occ e E). }
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

(** the expression diagnostics are empty exactly when the program types *)
Lemma expression_diags_empty_iff {p} (idx : Index.Snapshot.Syntax p) :
  expression_diags idx = nil <-> program_typedb p = true.
Proof.
  rewrite expression_diags_eq_spec. rewrite flat_map_nil_forallb, <- emits_none_program_typedb.
  rewrite !forallb_forall. split; intro H.
  - intros [r occ] Hin.
    assert (Hroc : exists ctx, In ((r, occ), ctx) (annotate_program idx)).
    { rewrite <- (annotate_program_fst idx) in Hin. apply in_map_iff in Hin. destruct Hin as [[ro ctx] [Hf Hi]].
      cbn [fst] in Hf. subst ro. exists ctx. exact Hi. }
    destruct Hroc as [ctx Hroc]. specialize (H _ Hroc). cbn [fst snd] in H.
    apply (occurrence_expr_diags_empty idx ctx r occ Hin).
    destruct (occurrence_expr_diags idx ctx (r, occ)); [reflexivity | discriminate H].
  - intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
    assert (Hin' : In (r, occ) (program_visit p)).
    { rewrite <- (annotate_program_fst idx). exact (in_map fst _ _ Hin). }
    specialize (H (r, occ) Hin'). cbn [snd] in H.
    apply (occurrence_expr_diags_empty idx ctx r occ Hin') in H. rewrite H. reflexivity.
Qed.

(* ---- PACKAGE main-count relation: # of top-level-decl occurrences per file = [file_main_count] ---- *)

Definition occurrence_main_count (occ : Index.Occurrence) : nat :=
  match Index.occurrence_role occ with Index.FileDeclaration _ => 1 | _ => 0 end.
Definition sum_main {A} (l : list (A * Index.Occurrence)) : nat :=
  fold_right (fun (ro : A * Index.Occurrence) (acc : nat) => (occurrence_main_count (snd ro) + acc)%nat) 0%nat l.

Lemma sum_main_cons {A} (x : A * Index.Occurrence) (l : list (A * Index.Occurrence)) :
  sum_main (x :: l) = (occurrence_main_count (snd x) + sum_main l)%nat.
Proof. reflexivity. Qed.

Lemma sum_main_app {A} (a b : list (A * Index.Occurrence)) :
  sum_main (a ++ b) = (sum_main a + sum_main b)%nat.
Proof.
  induction a as [|x a IH]; [reflexivity|].
  rewrite <- app_comm_cons, (sum_main_cons x (a ++ b)), (sum_main_cons x a), IH. lia.
Qed.

Lemma sum_main_operand : forall e parent me,
  sum_main (Index.occurrences_expr parent Index.ConversionOperand me e) = 0%nat.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent me;
    cbn [Index.occurrences_expr]; rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  1,2,3,4,5,6: reflexivity.
  rewrite Nat.add_0_l, sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd];
    rewrite Nat.add_0_l; apply IHx.
Qed.

Lemma sum_main_arg : forall e parent aidx me, sum_main (Index.occurrences_arg parent aidx me e) = 0%nat.
Proof.
  intros e parent aidx me. unfold Index.occurrences_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [Index.occurrences_expr]; rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  1,2,3,4,5,6: reflexivity.
  rewrite Nat.add_0_l, sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd];
    rewrite Nat.add_0_l; apply sum_main_operand.
Qed.

Lemma sum_main_args : forall es parent aidx me, sum_main (Index.occurrences_args parent aidx me es) = 0%nat.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [Index.occurrences_args]. rewrite sum_main_app, sum_main_arg, IH. reflexivity.
Qed.

Lemma sum_main_stmt : forall s parent sidx me, sum_main (Index.occurrences_stmt parent sidx me s) = 0%nat.
Proof.
  intros [args] parent sidx me. cbn [Index.occurrences_stmt].
  rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  rewrite Nat.add_0_l. apply sum_main_args.
Qed.

Lemma sum_main_stmts : forall ss parent sidx me, sum_main (Index.occurrences_stmts parent sidx me ss) = 0%nat.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [Index.occurrences_stmts]. rewrite sum_main_app, sum_main_stmt, IH. reflexivity.
Qed.

Lemma sum_main_decl : forall d parent didx me, sum_main (Index.occurrences_decl parent didx me d) = 1%nat.
Proof.
  intros [body] parent didx me. cbn [Index.occurrences_decl].
  rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  rewrite sum_main_stmts. reflexivity.
Qed.

Lemma sum_main_decls : forall ds parent didx me, sum_main (Index.occurrences_decls parent didx me ds) = length ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [Index.occurrences_decls length]. rewrite sum_main_app, sum_main_decl, IH. reflexivity.
Qed.

Lemma file_main_count_length : forall decls, file_main_count decls = length decls.
Proof.
  intro decls. unfold file_main_count.
  induction decls as [|[body] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sum_main_file : forall f, sum_main (Index.occurrences_file f) = file_main_count (Syntax.declarations f).
Proof.
  intros f. unfold Index.occurrences_file. destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  rewrite sum_main_cons; cbn [occurrence_main_count Index.occurrence_role snd].
  rewrite sum_main_decls, file_main_count_length. reflexivity.
Qed.

(* the package main buckets collect validated declaration references, agreeing with the counting view *)

Definition decl_kind_count (o : Index.Occurrence) : nat :=
  match Index.occurrence_kind o with Index.DeclarationKind => 1%nat | _ => 0%nat end.

Definition decl_count_list {A} (l : list (A * Index.Occurrence)) : nat :=
  fold_right (fun (ro : A * Index.Occurrence) (acc : nat) => (decl_kind_count (snd ro) + acc)%nat) 0%nat l.

Lemma decl_count_list_cons {A} (x : A * Index.Occurrence) (l : list (A * Index.Occurrence)) :
  decl_count_list (x :: l) = (decl_kind_count (snd x) + decl_count_list l)%nat.
Proof. reflexivity. Qed.

(** [decl_count_list] depends only on the OCCURRENCE component (the [snd]-projection). *)
Lemma decl_count_list_snd {A B} (l1 : list (A * Index.Occurrence)) (l2 : list (B * Index.Occurrence)) :
  map snd l1 = map snd l2 -> decl_count_list l1 = decl_count_list l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] Hm; cbn [map] in Hm; try discriminate; [reflexivity|].
  injection Hm as Hsnd Hrest.
  rewrite (decl_count_list_cons x l1), (decl_count_list_cons y l2), Hsnd, (IH l2 Hrest). reflexivity.
Qed.

(* ---- kind/role COHERENCE over a real occurrence stream: [decl_kind_count o = occurrence_main_count o]. ---- *)

Definition coh (o : Index.Occurrence) : Prop := decl_kind_count o = occurrence_main_count o.

Lemma coh_operand : forall e parent me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_expr parent Index.ConversionOperand me e).
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent me; cbn [Index.occurrences_expr].
  1,2,3,4,5,6: constructor; [ reflexivity | constructor ].
  constructor; [ reflexivity | constructor; [ reflexivity | apply IHx ] ].
Qed.

Lemma coh_arg : forall e parent aidx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_arg parent aidx me e).
Proof.
  intros e parent aidx me. unfold Index.occurrences_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ]; cbn [Index.occurrences_expr].
  1,2,3,4,5,6: constructor; [ reflexivity | constructor ].
  constructor; [ reflexivity | constructor; [ reflexivity | apply coh_operand ] ].
Qed.

Lemma coh_args : forall es parent aidx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_args parent aidx me es).
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [constructor|].
  cbn [Index.occurrences_args]. apply Forall_app. split; [ apply coh_arg | apply IH ].
Qed.

Lemma coh_stmt : forall s parent sidx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_stmt parent sidx me s).
Proof.
  intros [args] parent sidx me. cbn [Index.occurrences_stmt].
  constructor; [ reflexivity | apply coh_args ].
Qed.

Lemma coh_stmts : forall ss parent sidx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_stmts parent sidx me ss).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [constructor|].
  cbn [Index.occurrences_stmts]. apply Forall_app. split; [ apply coh_stmt | apply IH ].
Qed.

Lemma coh_decl : forall d parent didx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_decl parent didx me d).
Proof.
  intros [body] parent didx me. cbn [Index.occurrences_decl].
  constructor; [ reflexivity | apply coh_stmts ].
Qed.

Lemma coh_decls : forall ds parent didx me,
  Forall (fun ro => coh (snd ro)) (Index.occurrences_decls parent didx me ds).
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [constructor|].
  cbn [Index.occurrences_decls]. apply Forall_app. split; [ apply coh_decl | apply IH ].
Qed.

Lemma coh_file : forall f, Forall (fun ro => coh (snd ro)) (Index.occurrences_file f).
Proof.
  intro f. unfold Index.occurrences_file. destruct (Syntax.imports f) as [|i tl]; [| destruct i].
  constructor; [ reflexivity | ]. constructor; [ reflexivity | apply coh_decls ].
Qed.

(** the COHERENCE, transported to the [snd]-count identity: [decl_count_list = sum_main] over a file's occurrences. *)
Lemma decl_count_sum_main_file : forall f, decl_count_list (Index.occurrences_file f) = sum_main (Index.occurrences_file f).
Proof.
  intro f. pose proof (coh_file f) as Hcoh.
  induction (Index.occurrences_file f) as [|x l IH]; [reflexivity|].
  inversion Hcoh as [|? ? Hx Hl]; subst.
  rewrite (decl_count_list_cons x l), (sum_main_cons x l), (IH Hl). unfold coh in Hx. rewrite Hx. reflexivity.
Qed.

(* the shared arithmetic helpers the bucket-fold characterization reasons through *)
Definition olen {A} (o : option (list A)) : nat := match o with Some l => length l | None => 0%nat end.

Lemma olen_match {A} (o : option (list A)) :
  length (match o with Some l => l | None => [] end) = olen o.
Proof. destruct o; reflexivity. Qed.

(* the buckets are built as one fold over the delivered stream, not a second per-file traversal *)

Definition occurrence_pkg {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence) : string :=
  FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (fst ro))).

Definition program_package_step {p} (idx : Index.Snapshot.Syntax p)
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence) (acc : PackageMap.t (list (Index.DeclRef p)))
  : PackageMap.t (list (Index.DeclRef p)) :=
  match Index.as_decl idx (fst ro) with
  | Some dr => PackageMap.add (occurrence_pkg ro) (dr :: match PackageMap.find (occurrence_pkg ro) acc with Some l => l | None => [] end) acc
  | None =>
      match Index.as_kind idx (fst ro) Index.FileKind with
      | Some _ => match PackageMap.find (occurrence_pkg ro) acc with Some _ => acc | None => PackageMap.add (occurrence_pkg ro) [] acc end
      | None => acc
      end
  end.

(* the one shared bucket builder, folded by production over its own retained visit *)
Definition program_package_refs_from_visit {p} (idx : Index.Snapshot.Syntax p)
    (visit : list (Index.Snapshot.NodeRef p * Index.Occurrence)) : PackageMap.t (list (Index.DeclRef p)) :=
  fold_right (program_package_step idx) (PackageMap.empty (list (Index.DeclRef p))) visit.

Definition program_package_refs {p} (idx : Index.Snapshot.Syntax p) : PackageMap.t (list (Index.DeclRef p)) :=
  program_package_refs_from_visit idx (program_visit p).

(* the per-package main count over an occurrence list *)
Fixpoint package_declcount {p} (idx : Index.Snapshot.Syntax p) (dir : string)
    (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) : nat :=
  match l with
  | [] => 0%nat
  | ro :: rest =>
      ((if String.eqb (occurrence_pkg ro) dir
        then match Index.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
       + package_declcount idx dir rest)%nat
  end.

(* the per-step length contribution; a file-root init adds presence rather than length *)
Lemma program_package_step_olen {p} (idx : Index.Snapshot.Syntax p) (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
  (acc : PackageMap.t (list (Index.DeclRef p))) (dir : string) :
  olen (PackageMap.find dir (program_package_step idx ro acc))
  = ((if String.eqb (occurrence_pkg ro) dir then match Index.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
     + olen (PackageMap.find dir acc))%nat.
Proof.
  unfold program_package_step. destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PackageFacts.add_eq_o by reflexivity. cbn [olen length]. rewrite <- Edir, olen_match. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PackageFacts.add_neq_o by exact Edir. reflexivity.
  - destruct (Index.as_kind idx (fst ro) Index.FileKind) as [fnr|] eqn:Ef.
    + destruct (PackageMap.find (occurrence_pkg ro) acc) as [l|] eqn:Efind.
      * destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; rewrite Edir in Efind; rewrite Efind | ]; reflexivity.
      * destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PackageFacts.add_eq_o by reflexivity. cbn [olen length].
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PackageFacts.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Lemma program_package_olen_char {p} (idx : Index.Snapshot.Syntax p) : forall l acc dir,
  olen (PackageMap.find dir (fold_right (program_package_step idx) acc l)) = (package_declcount idx dir l + olen (PackageMap.find dir acc))%nat.
Proof.
  induction l as [|ro rest IH]; intros acc dir; [reflexivity|].
  cbn [fold_right package_declcount]. rewrite (program_package_step_olen idx ro (fold_right (program_package_step idx) acc rest) dir).
  rewrite (IH acc dir). lia.
Qed.

(* on a VISITED occurrence the DeclRef-mint contribution equals its [decl_kind_count]. *)
Lemma program_package_as_decl_kind_count {p} (idx : Index.Snapshot.Syntax p) (fr : Index.Snapshot.FileRef p)
  (r : Index.Snapshot.NodeRef p) (occ : Index.Occurrence) :
  In (r, occ) (Index.Snapshot.visit_file fr) ->
  (match Index.as_decl idx r with Some _ => 1%nat | None => 0%nat end) = decl_kind_count occ.
Proof.
  intro Hin. pose proof (Index.Snapshot.visit_file_view p fr r occ Hin) as [Hocc _].
  assert (Hk : Index.Snapshot.node_kind idx r = Index.occurrence_kind occ)
    by (rewrite (Index.Snapshot.node_kind_matches_source p idx r), Hocc; reflexivity).
  unfold Index.as_decl, Index.as_kind, decl_kind_count.
  destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx r) Index.DeclarationKind) as [He|Hne].
  - rewrite Hk in He; rewrite He; reflexivity.
  - rewrite Hk in Hne. destruct (Index.occurrence_kind occ); try reflexivity. exfalso; apply Hne; reflexivity.
Qed.

(* over a list sharing one package, the count is the whole list at that package and zero elsewhere *)
Lemma package_declcount_uniform {p} (idx : Index.Snapshot.Syntax p) (dir D : string)
  (L : list (Index.Snapshot.NodeRef p * Index.Occurrence)) :
  (forall ro, In ro L -> occurrence_pkg ro = D) ->
  (forall ro, In ro L -> match Index.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end = decl_kind_count (snd ro)) ->
  package_declcount idx dir L = (if String.eqb D dir then decl_count_list L else 0%nat).
Proof.
  induction L as [|ro rest IH]; intros Hpkg Hkind.
  - cbn [package_declcount decl_count_list]. destruct (String.eqb D dir); reflexivity.
  - cbn [package_declcount]. rewrite decl_count_list_cons.
    rewrite (Hpkg ro (or_introl eq_refl)), (Hkind ro (or_introl eq_refl)).
    rewrite (IH (fun ro' Hr => Hpkg ro' (or_intror Hr)) (fun ro' Hr => Hkind ro' (or_intror Hr))).
    destruct (String.eqb D dir); lia.
Qed.

(* a file block shares one package, so its count is the file's own when the package matches *)
Lemma package_declcount_binding {p} (idx : Index.Snapshot.Syntax p) (b : FilePath.T * Syntax.File) (dir : string) :
  In b (Syntax.file_bindings (Syntax.files p)) ->
  package_declcount idx dir (binding_visit p b)
  = (if String.eqb (FilePath.parent (fst b)) dir then file_main_count (Syntax.declarations (snd b)) else 0%nat).
Proof.
  intro Hb. unfold binding_visit.
  pose proof (Syntax.file_bindings_find (Syntax.files p) b Hb) as Hfind.
  destruct (Index.Snapshot.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop.
  rewrite (package_declcount_uniform idx dir (FilePath.parent (Index.Snapshot.file_ref_path fr)) (Index.Snapshot.visit_file fr)).
  - rewrite Hpath. destruct (String.eqb (FilePath.parent (fst b)) dir) eqn:E; [| reflexivity].
    rewrite (decl_count_list_snd (Index.Snapshot.visit_file fr) (Index.occurrences_file (Index.Snapshot.file_ref_source fr))
               (Index.Snapshot.visit_file_snd p fr)).
    rewrite decl_count_sum_main_file, sum_main_file, Hsrc. reflexivity.
  - intros [r occ] Hin. unfold occurrence_pkg; cbn [fst].
    destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
  - intros [r occ] Hin. cbn [fst snd]. exact (program_package_as_decl_kind_count idx fr r occ Hin).
Qed.

Lemma package_declcount_app {p} (idx : Index.Snapshot.Syntax p) (dir : string)
  (l1 l2 : list (Index.Snapshot.NodeRef p * Index.Occurrence)) :
  package_declcount idx dir (l1 ++ l2) = (package_declcount idx dir l1 + package_declcount idx dir l2)%nat.
Proof. induction l1 as [|ro l1 IH]; cbn [package_declcount app]; [reflexivity | rewrite IH; lia]. Qed.

(* the whole-program per-package count over the retained stream is the declarative one *)
Lemma package_declcount_prog_visit {p} (idx : Index.Snapshot.Syntax p) (dir : string) :
  package_declcount idx dir (program_visit p) = package_main_count dir (Syntax.files p).
Proof.
  rewrite program_visit_flat_map. unfold package_main_count.
  assert (H : forall L, (forall b, In b L -> In b (Syntax.file_bindings (Syntax.files p))) ->
             package_declcount idx dir (flat_map (binding_visit p) L) = list_dir_count dir L).
  { induction L as [|b rest IHL]; intro Hsub; [reflexivity|].
    cbn [flat_map list_dir_count]. rewrite package_declcount_app.
    rewrite (package_declcount_binding idx b dir (Hsub b (or_introl eq_refl))).
    rewrite (IHL (fun b' Hb' => Hsub b' (or_intror Hb'))). reflexivity. }
  apply H; intros b Hb; exact Hb.
Qed.

(** a present bucket's length is the package's declarative main count *)
Lemma program_package_refs_bucket_len {p} (idx : Index.Snapshot.Syntax p) : forall dir l,
  PackageMap.find dir (program_package_refs idx) = Some l -> length l = package_main_count dir (Syntax.files p).
Proof.
  intros dir l Hfind.
  assert (Holen : olen (PackageMap.find dir (program_package_refs idx)) = package_main_count dir (Syntax.files p)).
  { unfold program_package_refs, program_package_refs_from_visit. rewrite (program_package_olen_char idx (program_visit p) (PackageMap.empty _) dir).
    rewrite PackageFacts.empty_o. cbn [olen]. rewrite Nat.add_0_r. exact (package_declcount_prog_visit idx dir). }
  rewrite Hfind in Holen. cbn [olen] in Holen. exact Holen.
Qed.

(* an occurrence CONTRIBUTES its package to the bucket map iff it mints a DeclRef OR is a file root. *)
Definition program_package_contributes {p} (idx : Index.Snapshot.Syntax p) (ro : Index.Snapshot.NodeRef p * Index.Occurrence) : Prop :=
  Index.as_decl idx (fst ro) <> None \/ Index.as_kind idx (fst ro) Index.FileKind <> None.

Lemma program_package_step_some {p} (idx : Index.Snapshot.Syntax p) (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
  (acc : PackageMap.t (list (Index.DeclRef p))) (dir : string) :
  PackageMap.find dir (program_package_step idx ro acc) <> None
  <-> ((occurrence_pkg ro = dir /\ program_package_contributes idx ro) \/ PackageMap.find dir acc <> None).
Proof.
  unfold program_package_step, program_package_contributes.
  destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occurrence_pkg ro) dir) as [He|Hne].
    + rewrite He, PackageFacts.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | left; discriminate] | intros _; discriminate ].
    + rewrite PackageFacts.add_neq_o by exact Hne. split.
      * intro H; right; exact H.
      * intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
  - destruct (Index.as_kind idx (fst ro) Index.FileKind) as [fnr|] eqn:Ef.
    + destruct (PackageMap.find (occurrence_pkg ro) acc) as [l|] eqn:Efind.
      * split.
        -- intro H; right; exact H.
        -- intros [[He _]|H]; [ rewrite He in Efind; rewrite Efind; discriminate | exact H ].
      * destruct (string_dec (occurrence_pkg ro) dir) as [He|Hne].
        -- rewrite He, PackageFacts.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | right; discriminate] | intros _; discriminate ].
        -- rewrite PackageFacts.add_neq_o by exact Hne. split.
           ++ intro H; right; exact H.
           ++ intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
    + split.
      * intro H; right; exact H.
      * intros [[_ [Hd|Hf]]|H]; [ exfalso; apply Hd; reflexivity | exfalso; apply Hf; reflexivity | exact H ].
Qed.

Lemma program_package_find_some_iff {p} (idx : Index.Snapshot.Syntax p) : forall l acc dir,
  PackageMap.find dir (fold_right (program_package_step idx) acc l) <> None
  <-> ((exists ro, In ro l /\ occurrence_pkg ro = dir /\ program_package_contributes idx ro) \/ PackageMap.find dir acc <> None).
Proof.
  induction l as [|ro rest IH]; intros acc dir.
  - cbn [fold_right]. split; [ intro H; right; exact H | intros [[ro' [[] _]]|H]; exact H ].
  - cbn [fold_right]. rewrite (program_package_step_some idx ro (fold_right (program_package_step idx) acc rest) dir), (IH acc dir). split.
    + intros [Hstep|[[ro' [Hin' Hc']]|Hacc]].
      * left; exists ro; split; [left; reflexivity | exact Hstep].
      * left; exists ro'; split; [right; exact Hin' | exact Hc'].
      * right; exact Hacc.
    + intros [[ro' [[<-|Hin'] Hc']]|Hacc].
      * left; exact Hc'.
      * right; left; exists ro'; split; [exact Hin' | exact Hc'].
      * right; right; exact Hacc.
Qed.

(* the file ROOT is a [Index.FileKind] occurrence (so a file always contributes its package's presence). *)
Lemma root_node_kind {p} (idx : Index.Snapshot.Syntax p) (fr : Index.Snapshot.FileRef p) :
  Index.Snapshot.node_kind idx (Index.Snapshot.file_root_ref fr) = Index.FileKind.
Proof.
  rewrite (Index.Snapshot.node_kind_matches_source p idx (Index.Snapshot.file_root_ref fr)).
  pose proof (Index.Snapshot.source_occ_of_ref_eq (Index.Snapshot.file_root_ref fr)) as Hso.
  rewrite (Index.Snapshot.file_root_ref_file p fr), (Index.Snapshot.file_root_ref_local p fr) in Hso.
  assert (Hroot : In (Index.root_id, Index.MakeOccurrence Index.FileKind (Index.FileView (Index.Snapshot.file_ref_source fr))
                        None Index.FileRoot (Index.count_file (Index.Snapshot.file_ref_source fr)))
                     (Index.occurrences_file (Index.Snapshot.file_ref_source fr))).
  { unfold Index.occurrences_file. destruct (Syntax.imports (Index.Snapshot.file_ref_source fr)) as [|i tl]; [| destruct i].
    left; reflexivity. }
  apply Index.occurrences_file_exact in Hroot. rewrite Hso in Hroot. injection Hroot as Heq. rewrite Heq. reflexivity.
Qed.

Lemma root_ref_contributes {p} (idx : Index.Snapshot.Syntax p) (fr : Index.Snapshot.FileRef p) :
  program_package_contributes idx (Index.Snapshot.file_root_ref fr, Index.Snapshot.source_occurrence_of_ref (Index.Snapshot.file_root_ref fr)).
Proof.
  right. cbn [fst]. unfold Index.as_kind.
  destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx (Index.Snapshot.file_root_ref fr)) Index.FileKind) as [He|Hne];
    [ discriminate | exfalso; apply Hne; apply root_node_kind ].
Qed.

(** DOMAIN EXACTNESS (from the ONE visit-stream fold): a bucket is present iff a file has that parent directory. *)
Lemma program_package_refs_present {p} (idx : Index.Snapshot.Syntax p) : forall dir,
  PackageMap.In dir (program_package_refs idx) <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true.
Proof.
  intro dir. rewrite PackageFacts.in_find_iff. unfold program_package_refs, program_package_refs_from_visit.
  rewrite (program_package_find_some_iff idx (program_visit p) (PackageMap.empty _) dir). rewrite PackageFacts.empty_o. split.
  - intros [[[r occ] [Hin [Hpkg _]]]|Hne]; [| exfalso; apply Hne; reflexivity].
    (* the occurrence's file is in Syntax.files with parent dir *)
    rewrite program_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
    unfold binding_visit in Hrb. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
    destruct (Index.Snapshot.visit_file_view p fr r occ Hrb) as [_ Hfile].
    unfold occurrence_pkg in Hpkg. cbn [fst] in Hpkg. rewrite Hfile, (Index.Snapshot.file_of_path_sound p (fst b) fr Ef) in Hpkg.
    unfold list_dir_mem. apply existsb_exists. exists b. split; [exact Hb | apply String.eqb_eq; exact Hpkg].
  - intro Hmem. unfold list_dir_mem in Hmem. apply existsb_exists in Hmem. destruct Hmem as [b [Hb He]].
    apply String.eqb_eq in He.
    left. pose proof (Syntax.file_bindings_find (Syntax.files p) b Hb) as Hfind.
    destruct (Index.Snapshot.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath _]]].
    exists (Index.Snapshot.file_root_ref fr, Index.Snapshot.source_occurrence_of_ref (Index.Snapshot.file_root_ref fr)).
    split; [ | split; [ | apply root_ref_contributes ] ].
    + apply noderef_in_prog_visit.
    + unfold occurrence_pkg. cbn [fst]. rewrite (Index.Snapshot.file_root_ref_file p fr), Hpath. exact He.
Qed.

(** BELONGS: a main DeclRef in a package's bucket belongs to THAT package (its file's parent = the key). *)
Lemma program_package_mem {p} (idx : Index.Snapshot.Syntax p) : forall l acc dir d,
  In d (match PackageMap.find dir (fold_right (program_package_step idx) acc l) with Some x => x | None => [] end) ->
  (exists ro, In ro l /\ occurrence_pkg ro = dir /\ Index.as_decl idx (fst ro) = Some d)
  \/ In d (match PackageMap.find dir acc with Some x => x | None => [] end).
Proof.
  induction l as [|ro rest IH]; intros acc dir d Hin; [right; exact Hin|].
  cbn [fold_right] in Hin. unfold program_package_step at 1 in Hin.
  destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occurrence_pkg ro) dir) as [He|Hne].
    + rewrite He, PackageFacts.add_eq_o in Hin by reflexivity. destruct Hin as [<-|Hin].
      * left; exists ro; split; [left; reflexivity | split; [exact He | exact Ed]].
      * destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
          [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
    + rewrite PackageFacts.add_neq_o in Hin by exact Hne.
      destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
        [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
  - assert (Hin' : In d (match PackageMap.find dir (fold_right (program_package_step idx) acc rest) with Some x => x | None => [] end)).
    { destruct (Index.as_kind idx (fst ro) Index.FileKind) as [fnr|];
      [ destruct (PackageMap.find (occurrence_pkg ro) (fold_right (program_package_step idx) acc rest)) eqn:Efind;
        [ exact Hin | destruct (string_dec (occurrence_pkg ro) dir) as [He|Hne];
          [ rewrite He, PackageFacts.add_eq_o in Hin by reflexivity; rewrite <- He, Efind; exact Hin
          | rewrite PackageFacts.add_neq_o in Hin by exact Hne; exact Hin ] ]
      | exact Hin ]. }
    destruct (IH acc dir d Hin') as [[ro' [Hin2 [Hp' Hd']]]|Hrest];
      [ left; exists ro'; split; [right; exact Hin2 | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
Qed.

Lemma program_package_refs_belongs {p} (idx : Index.Snapshot.Syntax p) : forall dir l,
  PackageMap.find dir (program_package_refs idx) = Some l ->
  forall d, In d l ->
  FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref d))) = dir.
Proof.
  intros dir l Hfind d Hin.
  assert (Hb : In d (match PackageMap.find dir (program_package_refs idx) with Some x => x | None => [] end))
    by (rewrite Hfind; exact Hin).
  unfold program_package_refs, program_package_refs_from_visit in Hb.
  destruct (program_package_mem idx (program_visit p) (PackageMap.empty _) dir d Hb) as [[ro [_ [Hp Hd]]]|Hempty];
    [ | rewrite PackageFacts.empty_o in Hempty; destruct Hempty ].
  rewrite (Index.erase_as_kind idx (fst ro) Index.DeclarationKind d Hd). exact Hp.
Qed.

Lemma program_package_refs_singleton_on_success {p} (idx : Index.Snapshot.Syntax p) :
  current_grammar_one_main p -> forall dir l,
  PackageMap.find dir (program_package_refs idx) = Some l -> exists d, l = [d].
Proof.
  intros Hall dir l Hfind.
  pose proof (program_package_refs_bucket_len idx dir l Hfind) as Hlen.
  assert (Hmem : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true).
  { apply (program_package_refs_present idx dir). apply PackageFacts.in_find_iff. rewrite Hfind. discriminate. }
  assert (Hmt : PackageMap.MapsTo dir (MakePackageSummary (package_main_count dir (Syntax.files p))) (package_summaries (Syntax.files p))).
  { apply PackageFacts.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (Hall dir _ Hmt) as Hone. cbn [summary_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(* the package diagnostics anchor at a validated reference, and emptiness ties to the shared decision *)
Lemma elements_all_mapsto {p} (m : PackageMap.t (list (Index.DeclRef p))) : forall kv,
  In kv (PackageMap.elements m) -> PackageMap.MapsTo (fst kv) (snd kv) m.
Proof.
  intros [dir l] Hin. apply PackageFacts.elements_mapsto_iff, InA_alt.
  exists (dir, l). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma mapsto_in_elements {p} (m : PackageMap.t (list (Index.DeclRef p))) : forall dir l,
  PackageMap.MapsTo dir l m -> In (dir, l) (PackageMap.elements m).
Proof.
  intros dir l Hmt. apply PackageFacts.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
  destruct Hmt as [[dir' l'] [[Hk Hl] Hin]]. cbn in Hk, Hl. subst. exact Hin.
Qed.

Lemma bucket_key_present {p} (idx : Index.Snapshot.Syntax p) : forall dir l,
  PackageMap.MapsTo dir l (program_package_refs idx) -> package_present_b p dir = true.
Proof.
  intros dir l Hmt. unfold package_present_b.
  apply (proj1 (program_package_refs_present idx dir)). exists l. exact Hmt.
Qed.

(* the three package facts over an explicit stream, so elaboration can fold its own retained visit *)
Lemma package_refs_present_at {p} (idx : Index.Snapshot.Syntax p) visit (Hv : visit = program_visit p) :
  forall dir, PackageMap.In dir (program_package_refs_from_visit idx visit)
              <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true.
Proof. intro dir. rewrite Hv. exact (program_package_refs_present idx dir). Qed.

Lemma package_refs_bucket_len_at {p} (idx : Index.Snapshot.Syntax p) visit (Hv : visit = program_visit p) :
  forall dir l, PackageMap.find dir (program_package_refs_from_visit idx visit) = Some l ->
                length l = package_main_count dir (Syntax.files p).
Proof. intros dir l. rewrite Hv. exact (program_package_refs_bucket_len idx dir l). Qed.

Lemma package_refs_belongs_at {p} (idx : Index.Snapshot.Syntax p) visit (Hv : visit = program_visit p) :
  forall dir l, PackageMap.find dir (program_package_refs_from_visit idx visit) = Some l ->
  forall d, In d l ->
  FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref d))) = dir.
Proof. intros dir l. rewrite Hv. exact (program_package_refs_belongs idx dir l). Qed.

Definition package_diag_of_bucket {p} (m : PackageMap.t (list (Index.DeclRef p)))
    (Hpres : forall dir l, PackageMap.MapsTo dir l m -> package_present_b p dir = true)
    (dir : string) (l : list (Index.DeclRef p)) (Hmt : PackageMap.MapsTo dir l m)
    : list (DiagnosticReason p) :=
  match l with
  | nil        => [ MissingMainEntry (MakePackageRef p dir (Hpres dir l Hmt)) ]
  | d1 :: rest => map (fun dk => MainRedeclared dk d1) rest
  end.

Lemma package_diag_of_bucket_nil_iff {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres dir l Hmt :
  @package_diag_of_bucket p m Hpres dir l Hmt = nil <-> length l = 1%nat.
Proof.
  unfold package_diag_of_bucket; destruct l as [|d1 [|d2 rest]]; cbn [map length];
    split; intro H; solve [ reflexivity | discriminate H ].
Qed.

Fixpoint bucket_diags_elems {p} (m : PackageMap.t (list (Index.DeclRef p)))
    (Hpres : forall dir l, PackageMap.MapsTo dir l m -> package_present_b p dir = true)
    (es : list (string * list (Index.DeclRef p)))
    (Hall : forall kv, In kv es -> PackageMap.MapsTo (fst kv) (snd kv) m)
    : list (DiagnosticReason p) :=
  match es return (forall kv, In kv es -> PackageMap.MapsTo (fst kv) (snd kv) m) -> list (DiagnosticReason p) with
  | [] => fun _ => []
  | kv :: rest => fun H =>
      package_diag_of_bucket m Hpres (fst kv) (snd kv) (H kv (or_introl eq_refl))
      ++ bucket_diags_elems m Hpres rest (fun kv' Hin => H kv' (or_intror Hin))
  end Hall.

(* a package reference is its key, so the diagnostic does not depend on which presence proof made it *)
Lemma package_diag_of_bucket_proof_irrelevant {p} (m : PackageMap.t (list (Index.DeclRef p)))
    H1 H2 dir l Hmt1 Hmt2 :
  @package_diag_of_bucket p m H1 dir l Hmt1 = @package_diag_of_bucket p m H2 dir l Hmt2.
Proof.
  revert Hmt1 Hmt2. destruct l as [|d1 rest]; intros Hmt1 Hmt2; unfold package_diag_of_bucket.
  - do 2 f_equal. apply package_ref_key_inj. reflexivity.
  - reflexivity.
Qed.

Lemma bucket_diags_elems_proof_irrelevant {p} (m : PackageMap.t (list (Index.DeclRef p)))
    H1 H2 es Hall1 Hall2 :
  @bucket_diags_elems p m H1 es Hall1 = @bucket_diags_elems p m H2 es Hall2.
Proof.
  revert Hall1 Hall2. induction es as [|kv rest IH]; intros Hall1 Hall2; cbn [bucket_diags_elems].
  - reflexivity.
  - f_equal; [ apply package_diag_of_bucket_proof_irrelevant | apply IH ].
Qed.

Lemma bucket_diags_elems_nil_iff {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres es Hall :
  @bucket_diags_elems p m Hpres es Hall = nil <-> (forall kv, In kv es -> length (snd kv) = 1%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (package_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : package_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl)) = nil)
        by exact (proj2 (package_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin')) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

Definition package_diags {p} (idx : Index.Snapshot.Syntax p) : list (DiagnosticReason p) :=
  bucket_diags_elems (program_package_refs idx) (bucket_key_present idx)
    (PackageMap.elements (program_package_refs idx)) (elements_all_mapsto (program_package_refs idx)).

(** no package diagnostic exactly when every package has one main, decided from the retained buckets *)
Lemma package_diags_empty_iff_rules {p} (idx : Index.Snapshot.Syntax p) :
  package_diags idx = nil <-> PackageRulesValid p.
Proof.
  unfold package_diags. rewrite bucket_diags_elems_nil_iff.
  unfold PackageRulesValid, PackageDeclsUnique, MainPackagesHaveEntry. split.
  - intros Hbuck; split; intros dir s Hmt;
      (assert (Hpres : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true) by
         (pose proof (PackageMap.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
          destruct (list_dir_mem dir (Syntax.file_bindings (Syntax.files p))) eqn:E; [ reflexivity | discriminate Hf ]));
      destruct (proj2 (program_package_refs_present idx dir) Hpres) as [l Hbmt];
      assert (Hlen : length l = 1%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt);
      rewrite (package_summary_main_count (Syntax.files p) dir s Hmt);
      rewrite <- (program_package_refs_bucket_len idx dir l (PackageMap.find_1 Hbmt)); lia.
  - intros [Hle Hge] kv Hin.
    pose proof (elements_all_mapsto (program_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PackageMap.MapsTo (fst kv) (MakePackageSummary (package_main_count (fst kv) (Syntax.files p))) (package_summaries (Syntax.files p))).
    { apply PackageMap.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hle (fst kv) _ Hms) as Hle1. pose proof (Hge (fst kv) _ Hms) as Hge1.
    cbn [summary_main_count] in Hle1, Hge1.
    rewrite (program_package_refs_bucket_len idx (fst kv) (snd kv) (PackageMap.find_1 Hbmt)). lia.
Qed.

(** the same decision against the shared package half: one judgment with a production and a fixture view *)
Lemma package_diags_empty_iff {p} (idx : Index.Snapshot.Syntax p) : package_diags idx = nil <-> source_spec_package_rules_b p = true.
Proof. rewrite package_diags_empty_iff_rules, source_spec_package_rules_b_package_rules_valid. reflexivity. Qed.

(** the production diagnostics capture each factored rule exactly, one per redundant and one per missing *)
Definition diag_is_redeclared {p} (d : DiagnosticReason p) : bool :=
  match d with MainRedeclared _ _ => true | _ => false end.
Definition diag_is_missing_entry {p} (d : DiagnosticReason p) : bool :=
  match d with MissingMainEntry _ => true | _ => false end.

Lemma filter_redecl_map {p} (d1 : Index.DeclRef p) rest :
  filter diag_is_redeclared (map (fun dk => MainRedeclared dk d1) rest) = map (fun dk => MainRedeclared dk d1) rest.
Proof. induction rest as [|d2 rest' IH]; cbn [map filter diag_is_redeclared]; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma filter_missing_map {p} (d1 : Index.DeclRef p) rest :
  filter diag_is_missing_entry (map (fun dk => MainRedeclared dk d1) rest) = nil.
Proof. induction rest as [|d2 rest' IH]; cbn [map filter diag_is_missing_entry]; [ reflexivity | exact IH ]. Qed.

Lemma redecl_of_bucket_nil_iff {p} m Hpres dir l Hmt :
  filter diag_is_redeclared (@package_diag_of_bucket p m Hpres dir l Hmt) = nil <-> (length l <= 1)%nat.
Proof.
  unfold package_diag_of_bucket. destruct l as [|d1 rest].
  - cbn [length filter diag_is_redeclared]. split; intros _; [ lia | reflexivity ].
  - rewrite filter_redecl_map. cbn [length]. destruct rest as [|d2 rest'].
    + cbn [map length]. split; intros _; [ lia | reflexivity ].
    + cbn [map length]. split; intro H; [ discriminate H | exfalso; lia ].
Qed.

Lemma missing_of_bucket_nil_iff {p} m Hpres dir l Hmt :
  filter diag_is_missing_entry (@package_diag_of_bucket p m Hpres dir l Hmt) = nil <-> (1 <= length l)%nat.
Proof.
  unfold package_diag_of_bucket. destruct l as [|d1 rest].
  - cbn [length filter diag_is_missing_entry]. split; intro H; [ discriminate H | exfalso; lia ].
  - rewrite filter_missing_map. cbn [length]. split; intros _; [ lia | reflexivity ].
Qed.

Lemma redecl_diags_elems_nil_iff {p} m Hpres es Hall :
  filter diag_is_redeclared (@bucket_diags_elems p m Hpres es Hall) = nil
    <-> (forall kv, In kv es -> (length (snd kv) <= 1)%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - rewrite filter_app. split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (redecl_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : filter diag_is_redeclared (package_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) = nil)
        by exact (proj2 (redecl_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : filter diag_is_redeclared (bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin'))) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

Lemma missing_diags_elems_nil_iff {p} m Hpres es Hall :
  filter diag_is_missing_entry (@bucket_diags_elems p m Hpres es Hall) = nil
    <-> (forall kv, In kv es -> (1 <= length (snd kv))%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - rewrite filter_app. split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (missing_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : filter diag_is_missing_entry (package_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) = nil)
        by exact (proj2 (missing_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : filter diag_is_missing_entry (bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin'))) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

(** redeclaration diagnostics empty IFF [PackageDeclsUnique] (every package has AT MOST one main). *)
Lemma redecl_diags_empty_iff_rules {p} (idx : Index.Snapshot.Syntax p) :
  filter diag_is_redeclared (package_diags idx) = nil <-> PackageDeclsUnique p.
Proof.
  unfold package_diags. rewrite redecl_diags_elems_nil_iff. unfold PackageDeclsUnique. split.
  - intros Hbuck dir s Hmt.
    assert (Hpres : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true) by
      (pose proof (PackageMap.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
       destruct (list_dir_mem dir (Syntax.file_bindings (Syntax.files p))) eqn:E; [ reflexivity | discriminate Hf ]).
    destruct (proj2 (program_package_refs_present idx dir) Hpres) as [l Hbmt].
    assert (Hlen : (length l <= 1)%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt).
    rewrite (package_summary_main_count (Syntax.files p) dir s Hmt).
    rewrite <- (program_package_refs_bucket_len idx dir l (PackageMap.find_1 Hbmt)); lia.
  - intros Hle kv Hin.
    pose proof (elements_all_mapsto (program_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PackageMap.MapsTo (fst kv) (MakePackageSummary (package_main_count (fst kv) (Syntax.files p))) (package_summaries (Syntax.files p))).
    { apply PackageMap.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hle (fst kv) _ Hms) as Hle1. cbn [summary_main_count] in Hle1.
    rewrite (program_package_refs_bucket_len idx (fst kv) (snd kv) (PackageMap.find_1 Hbmt)). lia.
Qed.

(** missing-entry diagnostics empty IFF [MainPackagesHaveEntry] (every package has AT LEAST one main). *)
Lemma missing_diags_empty_iff_rules {p} (idx : Index.Snapshot.Syntax p) :
  filter diag_is_missing_entry (package_diags idx) = nil <-> MainPackagesHaveEntry p.
Proof.
  unfold package_diags. rewrite missing_diags_elems_nil_iff. unfold MainPackagesHaveEntry. split.
  - intros Hbuck dir s Hmt.
    assert (Hpres : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true) by
      (pose proof (PackageMap.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
       destruct (list_dir_mem dir (Syntax.file_bindings (Syntax.files p))) eqn:E; [ reflexivity | discriminate Hf ]).
    destruct (proj2 (program_package_refs_present idx dir) Hpres) as [l Hbmt].
    assert (Hlen : (1 <= length l)%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt).
    rewrite (package_summary_main_count (Syntax.files p) dir s Hmt).
    rewrite <- (program_package_refs_bucket_len idx dir l (PackageMap.find_1 Hbmt)); lia.
  - intros Hge kv Hin.
    pose proof (elements_all_mapsto (program_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PackageMap.MapsTo (fst kv) (MakePackageSummary (package_main_count (fst kv) (Syntax.files p))) (package_summaries (Syntax.files p))).
    { apply PackageMap.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hge (fst kv) _ Hms) as Hge1. cbn [summary_main_count] in Hge1.
    rewrite (program_package_refs_bucket_len idx (fst kv) (snd kv) (PackageMap.find_1 Hbmt)). lia.
Qed.

(* the one elaboration root: exact facts, or a nonempty structured diagnostic list *)

Lemma app_nil_iff {A} (l1 l2 : list A) : l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof. split; [ apply app_eq_nil | intros [-> ->]; reflexivity ]. Qed.

(* node-anchored diagnostics bucket into a standard map, so canonical order is the key order *)
Definition nkm_find {X} (k : Index.Key) (m : Index.KeyMap.t (list X)) : list X :=
  match Index.KeyMap.find k m with Some l => l | None => [] end.

Definition bucket_add {X} (kx : Index.Key * X)
    (m : Index.KeyMap.t (list X)) : Index.KeyMap.t (list X) :=
  Index.KeyMap.add (fst kx) (snd kx :: nkm_find (fst kx) m) m.

(* flatten node-keyed values into the Index.KeyMap-canonical order (path/local id). *)
Definition bucket_flatten {X} (kxs : list (Index.Key * X)) : list X :=
  flat_map snd (Index.KeyMap.elements
    (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs)).

(* if some key maps to a nonempty bucket, the whole flatten is nonempty (that bucket's elements are included). *)
Lemma nkm_find_flat_nonempty {X} (m : Index.KeyMap.t (list X)) (k : Index.Key) (b : list X) :
  Index.KeyMap.find k m = Some b -> b <> nil ->
  flat_map snd (Index.KeyMap.elements m) <> nil.
Proof.
  intros Hf Hb.
  apply Index.KeyFacts.find_mapsto_iff, Index.KeyFacts.elements_mapsto_iff, InA_alt in Hf.
  destruct Hf as [[k' b'] [[Hk Hb'] Hin]]. cbn in Hk, Hb'.
  intro Hnil. apply Hb. rewrite Hb'.
  assert (Hin2 : In b' (map snd (Index.KeyMap.elements m)))
    by (apply in_map_iff; exists (k', b'); split; [reflexivity | exact Hin]).
  clear -Hnil Hin2. revert Hnil Hin2. generalize (Index.KeyMap.elements m) as els.
  induction els as [|e els IH]; cbn [flat_map map]; [intros _ []|].
  intros Hnil Hin2. apply app_eq_nil in Hnil. destruct Hnil as [He Htl].
  destruct Hin2 as [<-|Hin2]; [exact He | apply IH; assumption].
Qed.

(* a nonempty keyed list flattens to a nonempty report: its first key holds a nonempty bucket. *)
Lemma bucket_flatten_cons_nonempty {X} (kx : Index.Key * X) (rest : list (Index.Key * X)) :
  bucket_flatten (kx :: rest) <> nil.
Proof.
  unfold bucket_flatten. cbn [fold_right]. unfold bucket_add at 1.
  set (m := fold_right bucket_add (Index.KeyMap.empty (list X)) rest).
  apply (nkm_find_flat_nonempty _ (fst kx) (snd kx :: nkm_find (fst kx) m)).
  - apply Index.key_map_add_equal.
  - discriminate.
Qed.

Lemma bucket_flatten_nil_iff {X} (kxs : list (Index.Key * X)) :
  bucket_flatten kxs = nil <-> kxs = nil.
Proof.
  split; [ | intros ->; reflexivity ].
  destruct kxs as [|kx rest]; [reflexivity|].
  intro H. exfalso. exact (bucket_flatten_cons_nonempty kx rest H).
Qed.

(* the node-primary key of a diagnostic (Some for the three node-anchored reasons; None for missing-main). *)
Definition diag_node_key {p} (d : DiagnosticReason p) : option Index.Key :=
  match diagnostic_primary d with AtNode r => Some (Index.Snapshot.node_ref_key r) | _ => None end.
Definition node_keyed {p} (l : list (DiagnosticReason p)) : list (Index.Key * DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some k => [(k, d)] | None => [] end) l.
Definition package_primary {p} (l : list (DiagnosticReason p)) : list (DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some _ => [] | None => [d] end) l.

Definition semantic_diagnostics (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) : list (DiagnosticReason p) :=
  bucket_flatten (node_keyed (expression_diags idx ++ package_diags idx))
  ++ package_primary (expression_diags idx ++ package_diags idx).

(* node_keyed and package_primary partition the diagnostics, so both empty iff the whole list is empty. *)
Lemma node_pkg_partition_nil {p} (l : list (DiagnosticReason p)) :
  node_keyed l = nil /\ package_primary l = nil <-> l = nil.
Proof.
  split; [ | intros ->; split; reflexivity ].
  destruct l as [|d rest]; [reflexivity|]. unfold node_keyed, package_primary; cbn [flat_map].
  destruct (diag_node_key d) as [k|]; cbn [app]; intros [H1 H2]; discriminate.
Qed.

Lemma semantic_diagnostics_empty_iff (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) :
  semantic_diagnostics p idx = nil <-> semantic_ok_b p = true.
Proof.
  unfold semantic_diagnostics. rewrite app_nil_iff, bucket_flatten_nil_iff, node_pkg_partition_nil, app_nil_iff.
  rewrite expression_diags_empty_iff, package_diags_empty_iff.
  unfold semantic_ok_b. rewrite Bool.andb_true_iff, expression_all_ok_program_typedb. reflexivity.
Qed.

Lemma semantic_diagnostics_nonempty (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) :
  semantic_ok_b p = false -> semantic_diagnostics p idx <> nil.
Proof.
  intros H Hc. apply (semantic_diagnostics_empty_iff p idx) in Hc. rewrite Hc in H. discriminate H.
Qed.

(* the bucketing commutes with a value transform, so the erased report is a source function *)

Lemma key_sorted_map_fst {A B} (f : A -> B) : forall l,
  Sorted (@Index.KeyMap.lt_key A) l ->
  Sorted (@Index.KeyMap.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma key_map_map_elements {A B} (f : A -> B) (m : Index.KeyMap.t A) :
  Index.KeyMap.elements (Index.KeyMap.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (Index.KeyMap.elements m).
Proof.
  apply Index.key_equal_list_key_element_equal.
  apply Index.KeyOrder.sort_equivlistA_eqlistA;
    [ apply Index.KeyMap.elements_3
    | apply key_sorted_map_fst, Index.KeyMap.elements_3 | ].
  intros [k e].
  rewrite <- Index.KeyFacts.elements_mapsto_iff, Index.KeyFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply Index.KeyFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. unfold Index.KeyOrderedType.eq in Hk. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. unfold Index.KeyOrderedType.eq in Hk. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply Index.KeyFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma nkmap_map_add {A B} (h : A -> B) (k : Index.Key) (v : A) (m : Index.KeyMap.t A) :
  Index.KeyMap.Equal (Index.KeyMap.map h (Index.KeyMap.add k v m))
                               (Index.KeyMap.add k (h v) (Index.KeyMap.map h m)).
Proof.
  intro k'. rewrite Index.KeyFacts.map_o.
  destruct (Index.KeyOrderedType.eq_dec k k') as [Heq|Hne].
  - rewrite !Index.KeyFacts.add_eq_o by exact Heq. reflexivity.
  - rewrite !Index.KeyFacts.add_neq_o by exact Hne. rewrite Index.KeyFacts.map_o. reflexivity.
Qed.

Lemma bucket_fold_map {X Y} (g : X -> Y) (kxs : list (Index.Key * X)) :
  Index.KeyMap.Equal
    (Index.KeyMap.map (map g) (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs))
    (fold_right bucket_add (Index.KeyMap.empty (list Y)) (map (fun kx => (fst kx, g (snd kx))) kxs)).
Proof.
  induction kxs as [|kx rest IH]; cbn [fold_right map].
  - intro k. rewrite Index.KeyFacts.map_o, !Index.KeyFacts.empty_o. reflexivity.
  - unfold bucket_add at 1 3. cbn [fst snd].
    set (M := fold_right bucket_add (Index.KeyMap.empty (list X)) rest) in *.
    set (M' := fold_right bucket_add (Index.KeyMap.empty (list Y))
                          (map (fun kx0 => (fst kx0, g (snd kx0))) rest)) in *.
    assert (Hfind : nkm_find (fst kx) M' = map g (nkm_find (fst kx) M)).
    { unfold nkm_find. rewrite <- (IH (fst kx)), Index.KeyFacts.map_o.
      destruct (Index.KeyMap.find (fst kx) M); reflexivity. }
    rewrite Hfind.
    transitivity (Index.KeyMap.add (fst kx)
                    (map g (snd kx :: nkm_find (fst kx) M)) (Index.KeyMap.map (map g) M)).
    + apply nkmap_map_add.
    + apply Index.KeyFacts.add_m; [reflexivity | reflexivity | exact IH].
Qed.

Lemma bucket_flatten_map {X Y} (g : X -> Y) (kxs : list (Index.Key * X)) :
  map g (bucket_flatten kxs) = bucket_flatten (map (fun kx => (fst kx, g (snd kx))) kxs).
Proof.
  unfold bucket_flatten.
  rewrite <- (Index.key_map_elements_equal _ _ (bucket_fold_map g kxs)).
  rewrite key_map_map_elements.
  generalize (Index.KeyMap.elements (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs)) as l.
  induction l as [|[k b] l IH]; cbn [flat_map map]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

(* the bucketing preserves the multiset, so the report reorders and never adds or drops a reason *)

Lemma flat_map_snd_mapsto {X} (m : Index.KeyMap.t (list X)) (d : X) :
  In d (flat_map snd (Index.KeyMap.elements m)) <->
  exists k b, Index.KeyMap.MapsTo k b m /\ In d b.
Proof.
  rewrite in_flat_map. split.
  - intros [[k b] [Hin Hd]]. cbn in Hd. exists k, b. split; [|exact Hd].
    apply Index.KeyFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [split; reflexivity | exact Hin].
  - intros [k [b [Hmt Hd]]].
    apply Index.KeyFacts.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' b'] [[Hk Hb] Hin]]. cbn in Hk, Hb.
    exists (k', b'). split; [exact Hin | cbn; rewrite <- Hb; exact Hd].
Qed.

Lemma flat_map_snd_add {X} (m : Index.KeyMap.t (list X)) (k : Index.Key) (v : list X) (d : X) :
  In d (flat_map snd (Index.KeyMap.elements (Index.KeyMap.add k v m))) <->
  In d v \/ In d (flat_map snd (Index.KeyMap.elements (Index.KeyMap.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. split.
  - intros [k' [b [Hmt Hd]]]. apply Index.KeyFacts.add_mapsto_iff in Hmt.
    destruct Hmt as [[Hk Hb]|[Hk Hmt]].
    + subst b. left; exact Hd.
    + right. exists k', b. split; [ apply Index.KeyFacts.remove_mapsto_iff; split; [exact Hk|exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + exists k, v. split; [ apply Index.KeyFacts.add_mapsto_iff; left; split; reflexivity | exact Hd ].
    + apply Index.KeyFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [ apply Index.KeyFacts.add_mapsto_iff; right; split; [exact Hk | exact Hmt] | exact Hd ].
Qed.

Lemma flat_map_snd_find {X} (m : Index.KeyMap.t (list X)) (k : Index.Key) (d : X) :
  In d (flat_map snd (Index.KeyMap.elements m)) <->
  In d (nkm_find k m) \/ In d (flat_map snd (Index.KeyMap.elements (Index.KeyMap.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. unfold nkm_find. split.
  - intros [k' [b [Hmt Hd]]]. destruct (Index.KeyOrderedType.eq_dec k k') as [Hk|Hk].
    + left. apply Index.KeyFacts.find_mapsto_iff in Hmt.
      rewrite (Index.KeyFacts.find_o m Hk), Hmt. exact Hd.
    + right. exists k', b. split; [ apply Index.KeyFacts.remove_mapsto_iff; split; [exact Hk | exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + destruct (Index.KeyMap.find k m) as [b0|] eqn:Ef; [ | destruct Hd ].
      exists k, b0. split; [ apply Index.KeyFacts.find_mapsto_iff; exact Ef | exact Hd ].
    + apply Index.KeyFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [exact Hmt | exact Hd].
Qed.

Lemma bucket_flatten_in {X} (kxs : list (Index.Key * X)) (d : X) :
  In d (bucket_flatten kxs) <-> In d (map snd kxs).
Proof.
  unfold bucket_flatten. induction kxs as [|kx rest IH]; cbn [fold_right map].
  - rewrite flat_map_snd_mapsto. split; [ intros [k [b [Hmt _]]]; revert Hmt; apply Index.KeyFacts.empty_mapsto_iff | intros [] ].
  - unfold bucket_add at 1.
    set (M := fold_right bucket_add (Index.KeyMap.empty (list X)) rest) in *.
    rewrite flat_map_snd_add. cbn [In].
    rewrite or_assoc, <- (flat_map_snd_find M (fst kx) d), IH. tauto.
Qed.

Lemma node_pkg_in {p} (l : list (DiagnosticReason p)) (d : DiagnosticReason p) :
  In d (map snd (node_keyed l)) \/ In d (package_primary l) <-> In d l.
Proof.
  induction l as [|d0 rest IH]; [cbn; tauto|].
  replace (node_keyed (d0 :: rest))
    with ((match diag_node_key d0 with Some k => [(k, d0)] | None => nil end) ++ node_keyed rest) by reflexivity.
  replace (package_primary (d0 :: rest))
    with ((match diag_node_key d0 with Some _ => nil | None => [d0] end) ++ package_primary rest) by reflexivity.
  rewrite map_app, !in_app_iff. cbn [In]. destruct (diag_node_key d0) as [k|]; cbn [map In]; rewrite <- IH; tauto.
Qed.

Lemma collect_diagnostics_in {p} (idx : Index.Snapshot.Syntax p) (d : DiagnosticReason p) :
  In d (semantic_diagnostics p idx) <-> In d (expression_diags idx ++ package_diags idx).
Proof.
  unfold semantic_diagnostics. rewrite in_app_iff, bucket_flatten_in. apply node_pkg_in.
Qed.

(** node-anchored diagnostics appear in strictly ascending key order, because the input keys are unique *)
Lemma node_keyed_self {p} (l : list (DiagnosticReason p)) :
  forall kd, In kd (node_keyed l) -> diag_node_key (snd kd) = Some (fst kd).
Proof.
  intros kd Hin. unfold node_keyed in Hin. apply in_flat_map in Hin. destruct Hin as [d [_ Hin]].
  destruct (diag_node_key d) as [k|] eqn:E; cbn [In] in Hin.
  - destruct Hin as [Heq|[]]. subst kd. cbn [fst snd]. exact E.
  - destruct Hin.
Qed.

(* the KEY list of a diagnostic list (the node-primary keys, in order). *)
Definition node_keys {p} (l : list (DiagnosticReason p)) : list Index.Key :=
  flat_map (fun d => match diag_node_key d with Some k => [k] | None => [] end) l.

Lemma node_keys_eq {p} (l : list (DiagnosticReason p)) : map fst (node_keyed l) = node_keys l.
Proof.
  induction l as [|d l IH]; [reflexivity|].
  replace (node_keyed (d :: l))
    with ((match diag_node_key d with Some k => [(k, d)] | None => nil end) ++ node_keyed l) by reflexivity.
  replace (node_keys (d :: l))
    with ((match diag_node_key d with Some k => [k] | None => nil end) ++ node_keys l) by reflexivity.
  rewrite map_app, IH. f_equal. destruct (diag_node_key d); reflexivity.
Qed.

Lemma node_keys_app {p} (l1 l2 : list (DiagnosticReason p)) : node_keys (l1 ++ l2) = node_keys l1 ++ node_keys l2.
Proof. unfold node_keys. rewrite flat_map_app. reflexivity. Qed.

(* at most one keyed value per source element, each carrying that element's key, gives a duplicate-free list *)
Lemma flat_map_le1_key_nodup {A} (key : A -> Index.Key) (f : A -> list Index.Key) (L : list A) :
  NoDup (map key L) ->
  (forall a, (length (f a) <= 1)%nat) ->
  (forall a b, In b (f a) -> b = key a) ->
  NoDup (flat_map f L).
Proof.
  intros Hnd Hf1 Hkey. induction L as [|a L IH]; [constructor|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  cbn [flat_map]. destruct (f a) as [|b [|b' rest]] eqn:Ef.
  - cbn [app]. apply IH; assumption.
  - cbn [app]. constructor.
    + rewrite (Hkey a b) by (rewrite Ef; left; reflexivity). intro Hin. apply Hnotin.
      apply in_flat_map in Hin. destruct Hin as [a0 [Ha0 Hb0]].
      rewrite (Hkey a0 _ Hb0). apply in_map. exact Ha0.
    + apply IH; assumption.
  - exfalso. pose proof (Hf1 a) as Hle. rewrite Ef in Hle. cbn [length] in Hle. lia.
Qed.

Lemma occurrence_expr_diags_le1 {p} (idx : Index.Snapshot.Syntax p) outer ro :
  (length (occurrence_expr_diags idx outer ro) <= 1)%nat.
Proof.
  unfold occurrence_expr_diags. destruct (Index.as_expr idx (fst ro)) as [er|]; [|cbn; lia].
  destruct (Index.view_expr (snd ro)) as [g|]; [|cbn; lia].
  destruct (local_conv_failure g) as [[t ci]|];
    [ destruct (conversion_target_ref idx er); [destruct (conversion_operand_ref idx er)|]; cbn; lia |].
  destruct (arg_default_failure (snd ro) g) as [[c dt]|]; cbn; lia.
Qed.

Lemma occurrence_expr_diags_key {p} (idx : Index.Snapshot.Syntax p) outer ro :
  forall d, In d (occurrence_expr_diags idx outer ro) -> diag_node_key d = Some (Index.Snapshot.node_ref_key (fst ro)).
Proof.
  intros d Hin. unfold occurrence_expr_diags in Hin.
  destruct (Index.as_expr idx (fst ro)) as [er|] eqn:Ea; [|destruct Hin].
  assert (Her : Index.erase_ref er = fst ro) by exact (Index.erase_as_kind idx (fst ro) Index.ExpressionKind er Ea).
  destruct (Index.view_expr (snd ro)) as [e|]; [|destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct (conversion_target_ref idx er) as [tr|]; [|destruct Hin].
    destruct (conversion_operand_ref idx er) as [opr|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [diag_node_key diagnostic_primary]. rewrite Her. reflexivity.
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [diag_node_key diagnostic_primary]. rewrite Her. reflexivity.
Qed.

Lemma flat_map_flat_map {A B C} (g : B -> list C) (h : A -> list B) (L : list A) :
  flat_map g (flat_map h L) = flat_map (fun x => flat_map g (h x)) L.
Proof. induction L as [|a L IH]; [reflexivity|]. cbn [flat_map]. rewrite flat_map_app, IH. reflexivity. Qed.

(* the per-occurrence keys of one occurrence's diagnostics: at most one, and it is the occurrence's key. *)
Lemma occurrence_node_keys_le1 {p} (idx : Index.Snapshot.Syntax p) outer ro :
  (length (node_keys (occurrence_expr_diags idx outer ro)) <= 1)%nat.
Proof.
  unfold node_keys.
  pose proof (occurrence_expr_diags_le1 idx outer ro) as Hle.
  destruct (occurrence_expr_diags idx outer ro) as [|d [|d' r]]; cbn [length flat_map app] in Hle |- *; [ lia | | lia ].
  destruct (diag_node_key d); cbn [length app]; lia.
Qed.

Lemma occurrence_node_keys_val {p} (idx : Index.Snapshot.Syntax p) outer ro :
  forall k, In k (node_keys (occurrence_expr_diags idx outer ro)) -> k = Index.Snapshot.node_ref_key (fst ro).
Proof.
  intros k Hin. unfold node_keys in Hin. apply in_flat_map in Hin. destruct Hin as [d [Hd Hk]].
  rewrite (occurrence_expr_diags_key idx outer ro d Hd) in Hk. cbn [In] in Hk. destruct Hk as [<-|[]]. reflexivity.
Qed.

Lemma expression_node_keys_nodup {p} (idx : Index.Snapshot.Syntax p) : NoDup (node_keys (expression_diags idx)).
Proof.
  unfold node_keys. rewrite expression_diags_eq_spec, flat_map_flat_map.
  apply (flat_map_le1_key_nodup (fun roc => Index.Snapshot.node_ref_key (fst (fst roc)))).
  - assert (H : map (fun roc => Index.Snapshot.node_ref_key (fst (fst roc))) (annotate_program idx)
                = map (fun ro => Index.Snapshot.node_ref_key (fst ro)) (program_visit p)).
    { rewrite <- (annotate_program_fst idx), map_map. reflexivity. }
    rewrite H. apply program_visit_key_nodup.
  - intro roc. exact (occurrence_node_keys_le1 idx (snd roc) (fst roc)).
  - intros roc k Hin. exact (occurrence_node_keys_val idx (snd roc) (fst roc) k Hin).
Qed.

(* the duplicate-main keys of one package bucket: the TAIL mains' occurrence keys. *)
Definition bucket_dup_keys {p} (l : list (Index.DeclRef p)) : list Index.Key :=
  match l with nil => nil | _ :: rest => map (fun dk => Index.Snapshot.node_ref_key (Index.erase_ref dk)) rest end.

Lemma node_keys_map_dup {p} (d1 : Index.DeclRef p) (rest : list (Index.DeclRef p)) :
  node_keys (map (fun dk => MainRedeclared dk d1) rest)
  = map (fun dk => Index.Snapshot.node_ref_key (Index.erase_ref dk)) rest.
Proof.
  induction rest as [|dk rest IH]; [reflexivity|].
  replace (node_keys (map (fun dk => MainRedeclared dk d1) (dk :: rest)))
    with ((match diag_node_key (MainRedeclared dk d1) with Some k => [k] | None => nil end)
          ++ node_keys (map (fun dk => MainRedeclared dk d1) rest)) by reflexivity.
  cbn [diag_node_key diagnostic_primary]. rewrite IH. reflexivity.
Qed.

Lemma package_diag_of_bucket_node_keys {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres dir l Hmt :
  node_keys (@package_diag_of_bucket p m Hpres dir l Hmt) = bucket_dup_keys l.
Proof.
  unfold package_diag_of_bucket, bucket_dup_keys. destruct l as [|d1 rest]; [reflexivity | apply node_keys_map_dup].
Qed.

Lemma bucket_diags_elems_node_keys {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres es Hall :
  node_keys (@bucket_diags_elems p m Hpres es Hall) = flat_map (fun kv => bucket_dup_keys (snd kv)) es.
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems flat_map]; [reflexivity|].
  rewrite node_keys_app, (package_diag_of_bucket_node_keys m Hpres (fst kv) (snd kv)), IH. reflexivity.
Qed.

Lemma package_node_keys_spec {p} (idx : Index.Snapshot.Syntax p) :
  node_keys (package_diags idx) = flat_map (fun kv => bucket_dup_keys (snd kv)) (PackageMap.elements (program_package_refs idx)).
Proof. unfold package_diags. apply bucket_diags_elems_node_keys. Qed.

Lemma in_nkm_find_mapsto {X} (k : Index.Key) (m : Index.KeyMap.t (list X)) (d : X) :
  In d (nkm_find k m) -> exists b, Index.KeyMap.MapsTo k b m /\ In d b.
Proof.
  unfold nkm_find. intro Hd. destruct (Index.KeyMap.find k m) as [b|] eqn:E.
  - exists b. split; [ apply Index.KeyFacts.find_mapsto_iff; exact E | exact Hd ].
  - exfalso; exact Hd.
Qed.

Lemma bucket_value_key {X} (key : X -> option Index.Key)
    (kxs : list (Index.Key * X)) (Hself : forall kd, In kd kxs -> key (snd kd) = Some (fst kd)) :
  forall k b, Index.KeyMap.MapsTo k b (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs) ->
  forall d, In d b -> key d = Some k.
Proof.
  induction kxs as [|kx rest IH]; intros k b Hmt d Hd.
  - apply Index.KeyFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - cbn [fold_right] in Hmt. unfold bucket_add in Hmt.
    apply Index.KeyFacts.add_mapsto_iff in Hmt. destruct Hmt as [[Hk Hb]|[Hk Hmt]].
    + subst b. unfold Index.KeyOrderedType.eq in Hk. subst k. cbn [In] in Hd. destruct Hd as [<-|Hd].
      * exact (Hself kx (or_introl eq_refl)).
      * apply in_nkm_find_mapsto in Hd. destruct Hd as [b0 [Hm0 Hd]].
        exact (IH (fun kd Hin => Hself kd (or_intror Hin)) (fst kx) b0 Hm0 d Hd).
    + exact (IH (fun kd Hin => Hself kd (or_intror Hin)) k b Hmt d Hd).
Qed.

Lemma nkmap_lt_key_trans {A} : forall (a b c : Index.Key * A),
  Index.KeyMap.lt_key a b -> Index.KeyMap.lt_key b c -> Index.KeyMap.lt_key a c.
Proof. intros [k1 ?] [k2 ?] [k3 ?]; unfold Index.KeyMap.lt_key; cbn; apply Index.KeyOrderedType.lt_trans. Qed.

(** the erased source report, comparable by equality and empty exactly when the source semantics accept *)
Definition erased_report (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) : list ErasedDiagnostic :=
  map erase_diagnostic (semantic_diagnostics p idx).

Lemma erased_report_empty_iff (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) :
  erased_report p idx = nil <-> semantic_ok_b p = true.
Proof.
  unfold erased_report. rewrite <- semantic_diagnostics_empty_iff.
  split; [ apply map_eq_nil | intro H; rewrite H; reflexivity ].
Qed.

(* the keyed visit stream is source-determined, depending only on the bindings and each file's occurrences *)
Lemma keyed_visit_file {p} (fr : Index.Snapshot.FileRef p) :
  map (fun rc => (Index.Snapshot.node_ref_key (fst rc), snd rc)) (Index.Snapshot.visit_file fr)
  = map (fun idocc => (Index.MakeKey (Index.Snapshot.file_ref_path fr) (fst idocc), snd idocc))
        (Index.occurrences_file (Index.Snapshot.file_ref_source fr)).
Proof.
  rewrite <- (Index.Snapshot.visit_file_idocc p fr), map_map.
  apply map_ext_in. intros [r occ] Hin. cbn [fst snd].
  rewrite Index.Snapshot.node_ref_key_eq.
  destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
Qed.

Lemma keyed_binding_visit (p : Syntax.Program) (b : FilePath.T * Syntax.File) :
  In b (Syntax.file_bindings (Syntax.files p)) ->
  map (fun rc => (Index.Snapshot.node_ref_key (fst rc), snd rc)) (binding_visit p b)
  = map (fun idocc => (Index.MakeKey (fst b) (fst idocc), snd idocc)) (Index.occurrences_file (snd b)).
Proof.
  intro Hin. unfold binding_visit.
  pose proof (Syntax.file_bindings_find (Syntax.files p) b Hin) as Hfind.
  destruct (Index.Snapshot.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, keyed_visit_file, Hpath, Hsrc. reflexivity.
Qed.

Definition keyed_visit (p : Syntax.Program) : list (Index.Key * Index.Occurrence) :=
  map (fun rc => (Index.Snapshot.node_ref_key (fst rc), snd rc)) (program_visit p).

Definition source_keyed_visit (fm : Syntax.Files) : list (Index.Key * Index.Occurrence) :=
  flat_map (fun b => map (fun idocc => (Index.MakeKey (fst b) (fst idocc), snd idocc)) (Index.occurrences_file (snd b)))
           (Syntax.file_bindings fm).

Lemma keyed_visit_source (p : Syntax.Program) : keyed_visit p = source_keyed_visit (Syntax.files p).
Proof.
  unfold keyed_visit, source_keyed_visit. rewrite program_visit_flat_map, map_flat_map.
  apply flat_map_ext_in. intros b Hin. exact (keyed_binding_visit p b Hin).
Qed.

(** semantically equal file maps have identical keyed streams *)
Lemma keyed_visit_files_equal (p1 p2 : Syntax.Program) :
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> keyed_visit p1 = keyed_visit p2.
Proof.
  intro Heq. rewrite !keyed_visit_source. unfold source_keyed_visit.
  assert (Hb : Syntax.file_bindings (Syntax.files p1) = Syntax.file_bindings (Syntax.files p2)).
  { unfold Syntax.file_bindings. apply Collections.file_elements_equal. exact Heq. }
  rewrite Hb. reflexivity.
Qed.

(** the enclosing context erases to a source function, because the keyed pass runs the same discipline *)
Definition erase_annot {p}
    (roc : (Index.Snapshot.NodeRef p * Index.Occurrence) * list (Index.ExprRef p))
  : (Index.Key * Index.Occurrence) * list Index.Key :=
  ((Index.Snapshot.node_ref_key (fst (fst roc)), snd (fst roc)),
   map (fun er => Index.Snapshot.node_ref_key (Index.erase_ref er)) (snd roc)).

Definition erase_estack {p} (stack : list (Index.ExprRef p * positive)) : list (Index.Key * positive) :=
  map (fun e => (Index.Snapshot.node_ref_key (Index.erase_ref (fst e)), snd e)) stack.

Fixpoint annotate_keyed (stack : list (Index.Key * positive))
    (stream : list (Index.Key * Index.Occurrence))
    : list ((Index.Key * Index.Occurrence) * list Index.Key) :=
  match stream with
  | [] => []
  | ke :: rest =>
      let open := filter (fun e => Pos.leb (Index.key_local (fst ke)) (snd e)) stack in
      let stack' := if is_conversion_occ (snd ke)
                    then (fst ke, Index.occurrence_subtree_end (snd ke)) :: open else open in
      (ke, map fst open) :: annotate_keyed stack' rest
  end.

(* a conversion occurrence (on a VALID reference whose occurrence is its source) HAS an [ExprRef] erasing to it. *)
Lemma is_conversion_occ_as_expr {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p) :
  is_conversion_occ (Index.Snapshot.source_occurrence_of_ref r) = true ->
  exists er, Index.as_expr idx r = Some er /\ Index.erase_ref er = r.
Proof.
  intro Hconv.
  assert (Hk : Index.Snapshot.node_kind idx r = Index.ExpressionKind).
  { rewrite (Index.Snapshot.node_kind_matches_source p idx r). unfold is_conversion_occ in Hconv.
    destruct (Index.view_expr (Index.Snapshot.source_occurrence_of_ref r)) as [e|] eqn:Ev;
      [ exact (Index.view_expr_kind _ e Ev) | discriminate Hconv ]. }
  unfold Index.as_expr. destruct (Index.as_kind_complete idx r Index.ExpressionKind Hk) as [tr [Has Her]].
  exists tr; split; [exact Has | exact Her].
Qed.

Lemma map_filter_comm {A B} (f : A -> B) (g : B -> bool) (h : A -> bool) (l : list A) :
  (forall a, g (f a) = h a) -> map f (filter h l) = filter g (map f l).
Proof.
  intro Hgh. induction l as [|a l IH]; [reflexivity|]. cbn [filter map].
  rewrite <- Hgh. destruct (g (f a)); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma erase_estack_filter {p} (l : positive) (stack : list (Index.ExprRef p * positive)) :
  erase_estack (filter (fun e => Pos.leb l (snd e)) stack)
  = filter (fun e => Pos.leb l (snd e)) (erase_estack stack).
Proof. unfold erase_estack. apply map_filter_comm. intro a. reflexivity. Qed.

(* THE SIMULATION: over a stream of VALID occurrences, the erased ref-annotation equals the keyed annotation. *)
Lemma annotate_encl_erased {p} (idx : Index.Snapshot.Syntax p) stack stream :
  (forall ro, In ro stream -> snd ro = Index.Snapshot.source_occurrence_of_ref (fst ro)) ->
  map erase_annot (annotate_encl idx stack stream)
  = annotate_keyed (erase_estack stack) (map (fun ro => (Index.Snapshot.node_ref_key (fst ro), snd ro)) stream).
Proof.
  revert stack. induction stream as [|ro rest IH]; intro stack; intro Hval; [reflexivity|].
  pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
  cbn [annotate_encl map annotate_keyed fst snd].
  assert (Hok : filter (fun e => Pos.leb (Index.key_local (Index.Snapshot.node_ref_key (fst ro))) (snd e))
                       (erase_estack stack)
              = erase_estack (filter (fun e => Pos.leb (Index.Snapshot.node_ref_local (fst ro)) (snd e)) stack)).
  { rewrite erase_estack_filter, Index.Snapshot.node_ref_key_eq. reflexivity. }
  f_equal.
  - unfold erase_annot. cbn [fst snd]. rewrite Hok. unfold erase_estack. rewrite !map_map. reflexivity.
  - rewrite (IH _ (fun ro' Hin => Hval ro' (or_intror Hin))), Hok. f_equal.
    destruct (is_conversion_occ (snd ro)) eqn:Hc.
    + assert (Hc' : is_conversion_occ (Index.Snapshot.source_occurrence_of_ref (fst ro)) = true)
        by (rewrite <- Hsrc; exact Hc).
      destruct (is_conversion_occ_as_expr idx (fst ro) Hc') as [er [Ha He]].
      rewrite Ha. cbn [erase_estack map fst snd]. rewrite He.
      rewrite (Index.Snapshot.node_subtree_end_matches_source p idx (fst ro)), <- Hsrc. reflexivity.
    + destruct (Index.as_expr idx (fst ro)) as [er|]; reflexivity.
Qed.

(* each per-file visited occurrence IS its reference's exact source occurrence (the validity the simulation needs). *)
Lemma binding_visit_valid (p : Syntax.Program) (b : FilePath.T * Syntax.File) :
  forall ro, In ro (binding_visit p b) -> snd ro = Index.Snapshot.source_occurrence_of_ref (fst ro).
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [Ho _]. exact Ho.
Qed.

(* the source enclosing-context annotation, a pure function of the file map *)
Definition annotate_source (fm : Syntax.Files)
  : list ((Index.Key * Index.Occurrence) * list Index.Key) :=
  flat_map (fun b => annotate_keyed []
              (map (fun idocc => (Index.MakeKey (fst b) (fst idocc), snd idocc)) (Index.occurrences_file (snd b))))
           (Syntax.file_bindings fm).

Lemma annotate_program_erased {p} (idx : Index.Snapshot.Syntax p) :
  map erase_annot (annotate_program idx) = annotate_source (Syntax.files p).
Proof.
  unfold annotate_program, program_blocks. rewrite flat_map_map.
  unfold annotate_source. rewrite map_flat_map.
  apply flat_map_ext_in. intros b Hin.
  rewrite (annotate_encl_erased idx [] (binding_visit p b) (binding_visit_valid p b)).
  cbn [erase_estack]. f_equal. exact (keyed_binding_visit p b Hin).
Qed.

(** erasing the retained annotated object reproduces the pure-source annotation's expression projection *)
Lemma annotated_forest_erased_source {p} {input : Input p}
    (forest : WorkForest input) (aw : AnnotatedWork forest) :
  map (fun x => erase_annot (work_pair_ctx x)) (annotated_items aw)
  = filter (fun kc => match Index.view_expr (snd (fst kc)) with Some _ => true | None => false end)
           (annotate_source (Syntax.files p)).
Proof.
  etransitivity.
  { symmetry. apply (map_map work_pair_ctx erase_annot (annotated_items aw)). }
  rewrite (annotated_align_eq aw).
  rewrite (map_filter_comm erase_annot
             (fun kc => match Index.view_expr (snd (fst kc)) with Some _ => true | None => false end)
             (fun rc => occurrence_is_expr (fst rc)) (annotate_program (index input))
             (fun a => ltac:(destruct a as [[r occ] ctx]; cbn [erase_annot occurrence_is_expr fst snd]; reflexivity))).
  rewrite (annotate_program_erased (index input)). reflexivity.
Qed.

Lemma annotate_source_files_equal (fm1 fm2 : Syntax.Files) :
  Syntax.FilesEqual fm1 fm2 -> annotate_source fm1 = annotate_source fm2.
Proof.
  intro Heq. unfold annotate_source.
  assert (Hb : Syntax.file_bindings fm1 = Syntax.file_bindings fm2)
    by (unfold Syntax.file_bindings; apply Collections.file_elements_equal; exact Heq).
  rewrite Hb. reflexivity.
Qed.


(* the same decision over erased data: a pure source function of key, occurrence and context *)
Definition erase_occ_diags (kroc : (Index.Key * Index.Occurrence) * list Index.Key)
  : list ErasedDiagnostic :=
  match Index.view_expr (snd (fst kroc)) with
  | None => []
  | Some e =>
      match local_conv_failure e with
      | Some (t, _) => [ MakeErased CodeInvalidConversion (AnchorNode (fst (fst kroc)))
                                            (map AnchorNode (snd kroc)) (Some t) None (expression_conv_target e) ]
      | None =>
          match arg_default_failure (snd (fst kroc)) e with
          | Some (_, dt) => [ MakeErased CodeDefaultNotRepresentable (AnchorNode (fst (fst kroc))) [] (Some dt) None None ]
          | None => []
          end
      end
  end.

(* erasing the two expression diagnostics, computed explicitly (isolating the anchor/target projection). *)
Lemma erase_diagnostic_invalid {p} (er : Index.ExprRef p) tr opr outer t ci :
  erase_diagnostic (InvalidConversion er tr opr outer t ci)
  = MakeErased CodeInvalidConversion (AnchorNode (Index.Snapshot.node_ref_key (Index.erase_ref er)))
      (map (fun r => AnchorNode (Index.Snapshot.node_ref_key (Index.erase_ref r))) outer) (Some t) None
      (Index.type_name_ref_syntax tr).
Proof.
  unfold erase_diagnostic.
  cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erased_source_target erase_anchor].
  rewrite map_map. reflexivity.
Qed.

Lemma erase_diagnostic_default {p} (er : Index.ExprRef p) c dt :
  erase_diagnostic (DefaultNotRepresentable er c dt)
  = MakeErased CodeDefaultNotRepresentable (AnchorNode (Index.Snapshot.node_ref_key (Index.erase_ref er))) [] (Some dt) None None.
Proof. reflexivity. Qed.

(* erasing the emitted diagnostics equals the keyed emitter, with membership ruling out the dead branch *)
Lemma erase_occ_diags_eq {p} (idx : Index.Snapshot.Syntax p) (r : Index.Snapshot.NodeRef p) occ ctx :
  In (r, occ) (program_visit p) ->
  map erase_diagnostic (occurrence_expr_diags idx ctx (r, occ)) = erase_occ_diags (erase_annot ((r, occ), ctx)).
Proof.
  intro Hin.
  assert (Hval : occ = Index.Snapshot.source_occurrence_of_ref r) by exact (program_visit_view p r occ Hin).
  unfold occurrence_expr_diags, erase_occ_diags, erase_annot. cbn [fst snd].
  destruct (Index.as_expr idx r) as [er|] eqn:Ea.
  - assert (Hk : Index.Snapshot.node_kind idx r = Index.ExpressionKind).
    { unfold Index.as_expr, Index.as_kind in Ea.
      destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx r) Index.ExpressionKind) as [He|]; [exact He|discriminate Ea]. }
    assert (Hke : Index.occurrence_kind occ = Index.ExpressionKind)
      by (rewrite Hval, <- (Index.Snapshot.node_kind_matches_source p idx r); exact Hk).
    destruct (Index.kind_view_expr occ Hke) as [e Hv]. rewrite Hv.
    assert (Her : Index.erase_ref er = r) by exact (Index.erase_as_kind idx r Index.ExpressionKind er Ea).
    destruct (local_conv_failure e) as [[t ci]|] eqn:Elc.
    + destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate Elc.
      destruct (conversion_target_ref_conv idx r occ er ts x Hin Hv Ea) as [tr [Hctr [_ [_ Hsyn]]]].
      destruct (conversion_operand_ref_conv idx r occ er ts x Hin Hv Ea) as [opr [Hcor _]].
      rewrite Hctr, Hcor. cbn [map]. rewrite erase_diagnostic_invalid, Her, map_map, Hsyn.
      cbn [expression_conv_target]. reflexivity.
    + destruct (arg_default_failure occ e) as [[c dt]|].
      * cbn [map]. rewrite erase_diagnostic_default, Her. reflexivity.
      * reflexivity.
  - assert (Hkne : Index.Snapshot.node_kind idx r <> Index.ExpressionKind).
    { unfold Index.as_expr, Index.as_kind in Ea.
      destruct (Index.syntaxkind_eq_dec (Index.Snapshot.node_kind idx r) Index.ExpressionKind); [discriminate Ea|assumption]. }
    assert (Hvne : Index.view_expr occ = None).
    { destruct (Index.view_expr occ) as [e|] eqn:E; [|reflexivity]. exfalso. apply Hkne.
      rewrite (Index.Snapshot.node_kind_matches_source p idx r), <- Hval. exact (Index.view_expr_kind occ e E). }
    rewrite Hvne. reflexivity.
Qed.

(* the erased expression report over the annotated program = the keyed emitter over each occurrence. *)
Lemma erased_expr_diags_annot {p} (idx : Index.Snapshot.Syntax p) :
  map erase_diagnostic (expression_diags idx)
  = flat_map (fun roc => erase_occ_diags (erase_annot roc)) (annotate_program idx).
Proof.
  rewrite expression_diags_eq_spec, map_flat_map. apply flat_map_ext_in.
  intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
  apply erase_occ_diags_eq.
  pose proof (in_map fst _ _ Hin) as Hin'. rewrite annotate_program_fst in Hin'. cbn [fst] in Hin'.
  exact Hin'.
Qed.

(** the erased EXPRESSION report is a SOURCE function of the file map (via [annotate_source]). *)
Lemma erased_expr_diags_source {p} (idx : Index.Snapshot.Syntax p) :
  map erase_diagnostic (expression_diags idx) = flat_map erase_occ_diags (annotate_source (Syntax.files p)).
Proof.
  rewrite erased_expr_diags_annot, <- (annotate_program_erased idx), flat_map_map. reflexivity.
Qed.

(** the package buckets erase to a source function, because the keyed pass groups identically *)

Definition erase_dkey {p} (dr : Index.DeclRef p) : Index.Key := Index.Snapshot.node_ref_key (Index.erase_ref dr).
Definition occurrence_pkg_key (ke : Index.Key * Index.Occurrence) : string :=
  FilePath.parent (Index.key_path (fst ke)).

Definition keyed_program_package_step (ke : Index.Key * Index.Occurrence) (acc : PackageMap.t (list Index.Key))
  : PackageMap.t (list Index.Key) :=
  match Index.occurrence_kind (snd ke) with
  | Index.DeclarationKind =>
      PackageMap.add (occurrence_pkg_key ke) (fst ke :: match PackageMap.find (occurrence_pkg_key ke) acc with Some l => l | None => [] end) acc
  | Index.FileKind =>
      match PackageMap.find (occurrence_pkg_key ke) acc with Some _ => acc | None => PackageMap.add (occurrence_pkg_key ke) [] acc end
  | _ => acc
  end.

Definition keyed_buckets (l : list (Index.Key * Index.Occurrence)) : PackageMap.t (list Index.Key) :=
  fold_right keyed_program_package_step (PackageMap.empty (list Index.Key)) l.

(* the keyed package of an occurrence equals its source parent directory (via [node_ref_key_eq]). *)
Lemma occurrence_pkg_key_eq {p} (ro : Index.Snapshot.NodeRef p * Index.Occurrence) :
  occurrence_pkg_key (Index.Snapshot.node_ref_key (fst ro), snd ro) = occurrence_pkg ro.
Proof.
  unfold occurrence_pkg_key, occurrence_pkg. cbn [fst]. rewrite Index.Snapshot.node_ref_key_eq. reflexivity.
Qed.

Lemma program_package_erased_find {p} (idx : Index.Snapshot.Syntax p) (L : list (Index.Snapshot.NodeRef p * Index.Occurrence)) :
  (forall ro, In ro L -> snd ro = Index.Snapshot.source_occurrence_of_ref (fst ro)) ->
  forall k, PackageMap.find k (PackageMap.map (map erase_dkey) (fold_right (program_package_step idx) (PackageMap.empty _) L))
          = PackageMap.find k (keyed_buckets (map (fun ro => (Index.Snapshot.node_ref_key (fst ro), snd ro)) L)).
Proof.
  induction L as [|ro L IH]; intro Hval.
  - intro k. rewrite PackageFacts.map_o. cbn [fold_right map keyed_buckets]. rewrite !PackageFacts.empty_o. reflexivity.
  - pose proof (IH (fun ro' Hin => Hval ro' (or_intror Hin))) as IHk.
    unfold keyed_buckets in IHk.
    pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
    assert (Hk : Index.Snapshot.node_kind idx (fst ro) = Index.occurrence_kind (snd ro))
      by (rewrite (Index.Snapshot.node_kind_matches_source p idx (fst ro)), <- Hsrc; reflexivity).
    intro k. cbn [fold_right map keyed_buckets].
    set (acc := fold_right (program_package_step idx) (PackageMap.empty (list (Index.DeclRef p))) L) in *.
    set (kacc := fold_right keyed_program_package_step (PackageMap.empty (list Index.Key))
                   (map (fun ro => (Index.Snapshot.node_ref_key (fst ro), snd ro)) L)) in *.
    unfold program_package_step at 1, keyed_program_package_step at 1. cbn [fst snd]. rewrite occurrence_pkg_key_eq.
    destruct (Index.occurrence_kind (snd ro)) eqn:Hok.
    + (* Index.FileKind: as_decl = None, as_kind Index.FileKind = Some — file-root init (presence, not length) *)
      assert (Hd : Index.as_decl idx (fst ro) = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      destruct (Index.as_kind_complete idx (fst ro) Index.FileKind) as [fr [Hf _]]; [rewrite Hk; reflexivity|].
      rewrite Hd, Hf.
      pose proof (IHk (occurrence_pkg ro)) as IHo. rewrite PackageFacts.map_o in IHo. rewrite <- IHo.
      destruct (PackageMap.find (occurrence_pkg ro) acc) as [la|] eqn:Ea; cbn [option_map].
      * exact (IHk k).
      * destruct (String.eqb (occurrence_pkg ro) k) eqn:Ek.
        -- apply String.eqb_eq in Ek. rewrite PackageFacts.map_o, PackageFacts.add_eq_o, PackageFacts.add_eq_o by exact Ek. reflexivity.
        -- apply String.eqb_neq in Ek. rewrite PackageFacts.map_o, PackageFacts.add_neq_o, PackageFacts.add_neq_o by exact Ek.
           rewrite <- PackageFacts.map_o. exact (IHk k).
    + (* Index.PackageClauseKind: neither *)
      assert (Hd : Index.as_decl idx (fst ro) = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : Index.as_kind idx (fst ro) Index.FileKind = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* Index.DeclarationKind: as_decl = Some dr — a main is prepended; its erased key IS the occurrence's key *)
      destruct (Index.as_kind_complete idx (fst ro) Index.DeclarationKind) as [dr [Hdr Her]];
        [ rewrite Hk; reflexivity | ].
      unfold Index.as_decl. rewrite Hdr.
      pose proof (IHk (occurrence_pkg ro)) as IHo. rewrite PackageFacts.map_o in IHo.
      destruct (String.eqb (occurrence_pkg ro) k) eqn:Ek.
      * apply String.eqb_eq in Ek. rewrite PackageFacts.map_o, PackageFacts.add_eq_o, PackageFacts.add_eq_o by exact Ek.
        cbn [option_map map]. unfold erase_dkey. rewrite Her. f_equal. f_equal.
        rewrite <- IHo. destruct (PackageMap.find (occurrence_pkg ro) acc) as [la|]; reflexivity.
      * apply String.eqb_neq in Ek. rewrite PackageFacts.map_o, PackageFacts.add_neq_o, PackageFacts.add_neq_o by exact Ek.
        rewrite <- PackageFacts.map_o. exact (IHk k).
    + (* Index.StatementKind: neither *)
      assert (Hd : Index.as_decl idx (fst ro) = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : Index.as_kind idx (fst ro) Index.FileKind = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* Index.ExpressionKind: neither *)
      assert (Hd : Index.as_decl idx (fst ro) = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : Index.as_kind idx (fst ro) Index.FileKind = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* Index.TypeNameKind: neither (a conversion's source type name is not a decl or file) *)
      assert (Hd : Index.as_decl idx (fst ro) = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : Index.as_kind idx (fst ro) Index.FileKind = None)
        by (apply Index.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
Qed.

(* the erased buckets of the retained elaboration equal the keyed source buckets *)
Lemma program_package_refs_erased {p} (idx : Index.Snapshot.Syntax p) :
  PackageMap.Equal (PackageMap.map (map erase_dkey) (program_package_refs idx)) (keyed_buckets (keyed_visit p)).
Proof.
  intro k. unfold program_package_refs, program_package_refs_from_visit, keyed_visit.
  apply (program_package_erased_find idx (program_visit p)).
  intros [r occ] Hin. exact (program_visit_view p r occ Hin).
Qed.

(* the ERASED package diagnostics of one bucket, over its erased (Index.Key) keys — a pure source function. *)
Definition erase_bucket_diag (kv : string * list Index.Key) : list ErasedDiagnostic :=
  match snd kv with
  | nil        => [ MakeErased CodeMissingMainEntry (AnchorPackage (fst kv)) [] None None None ]
  | e1 :: erest => map (fun ek => MakeErased CodeMainRedeclared (AnchorNode ek) [AnchorNode e1] None None None) erest
  end.

Lemma package_diag_of_bucket_erased {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres dir l Hmt :
  map erase_diagnostic (@package_diag_of_bucket p m Hpres dir l Hmt)
  = erase_bucket_diag (dir, map erase_dkey l).
Proof.
  unfold package_diag_of_bucket, erase_bucket_diag. cbn [snd]. destruct l as [|d1 rest]; cbn [map].
  - unfold erase_diagnostic. cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erase_anchor].
    reflexivity.
  - rewrite !map_map. unfold erase_diagnostic, erase_dkey.
    cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erase_anchor map]. reflexivity.
Qed.

Lemma bucket_diags_elems_erased {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres es Hall :
  map erase_diagnostic (@bucket_diags_elems p m Hpres es Hall)
  = flat_map erase_bucket_diag (map (fun kv => (fst kv, map erase_dkey (snd kv))) es).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems map flat_map]; [reflexivity|].
  rewrite map_app, IH. f_equal. apply package_diag_of_bucket_erased.
Qed.

(** the erased PACKAGE report is a SOURCE function of the file map (via the keyed source buckets). *)
Lemma erased_pkg_diags_source {p} (idx : Index.Snapshot.Syntax p) :
  map erase_diagnostic (package_diags idx)
  = flat_map erase_bucket_diag (PackageMap.elements (keyed_buckets (keyed_visit p))).
Proof.
  unfold package_diags. rewrite bucket_diags_elems_erased.
  rewrite <- Collections.package_map_elements.
  rewrite (Collections.package_elements_equal _ _ (program_package_refs_erased idx)). reflexivity.
Qed.

Lemma erased_pkg_diags_files_equal (p1 p2 : Syntax.Program)
    (idx1 : Index.Snapshot.Syntax p1) (idx2 : Index.Snapshot.Syntax p2) :
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) ->
  map erase_diagnostic (package_diags idx1) = map erase_diagnostic (package_diags idx2).
Proof.
  intro Heq. rewrite !erased_pkg_diags_source, (keyed_visit_files_equal p1 p2 Heq). reflexivity.
Qed.

(** the whole erased report as a pure source function of the file map *)
Definition enode_key (e : ErasedDiagnostic) : option Index.Key :=
  match erased_primary e with AnchorNode k => Some k | _ => None end.
Definition enode_keyed (l : list ErasedDiagnostic) : list (Index.Key * ErasedDiagnostic) :=
  flat_map (fun e => match enode_key e with Some k => [(k, e)] | None => [] end) l.
Definition epkg_primary (l : list ErasedDiagnostic) : list ErasedDiagnostic :=
  flat_map (fun e => match enode_key e with Some _ => [] | None => [e] end) l.

(* the raw erased source diagnostics: expression scars, then the keyed source package buckets *)
Definition erased_src_diags (fm : Syntax.Files) : list ErasedDiagnostic :=
  flat_map erase_occ_diags (annotate_source fm)
  ++ flat_map erase_bucket_diag (PackageMap.elements (keyed_buckets (source_keyed_visit fm))).

(** the whole erased report in canonical order, bucketed by key and flattened in path and local order *)
Definition erased_report_src (fm : Syntax.Files) : list ErasedDiagnostic :=
  bucket_flatten (enode_keyed (erased_src_diags fm)) ++ epkg_primary (erased_src_diags fm).

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

Lemma package_primary_erase {p} (l : list (DiagnosticReason p)) :
  map erase_diagnostic (package_primary l) = epkg_primary (map erase_diagnostic l).
Proof.
  induction l as [|d rest IH]; [reflexivity|].
  replace (package_primary (d :: rest))
    with ((match diag_node_key d with Some _ => nil | None => [d] end) ++ package_primary rest) by reflexivity.
  replace (epkg_primary (map erase_diagnostic (d :: rest)))
    with ((match enode_key (erase_diagnostic d) with Some _ => nil | None => [erase_diagnostic d] end)
          ++ epkg_primary (map erase_diagnostic rest)) by reflexivity.
  rewrite map_app, IH, enode_key_erase. destruct (diag_node_key d) as [k|]; reflexivity.
Qed.

Lemma erased_src_diags_eq {p} (idx : Index.Snapshot.Syntax p) :
  map erase_diagnostic (expression_diags idx ++ package_diags idx) = erased_src_diags (Syntax.files p).
Proof.
  unfold erased_src_diags. rewrite map_app, erased_expr_diags_source, erased_pkg_diags_source, keyed_visit_source.
  reflexivity.
Qed.

Lemma erased_report_src_eq {p} (idx : Index.Snapshot.Syntax p) :
  erased_report p idx = erased_report_src (Syntax.files p).
Proof.
  unfold erased_report, erased_report_src, semantic_diagnostics. rewrite map_app. f_equal.
  - rewrite (bucket_flatten_map erase_diagnostic (node_keyed (expression_diags idx ++ package_diags idx))).
    rewrite node_keyed_erase, erased_src_diags_eq. reflexivity.
  - rewrite package_primary_erase, erased_src_diags_eq. reflexivity.
Qed.

Lemma erased_src_diags_files_equal (fm1 fm2 : Syntax.Files) :
  Syntax.FilesEqual fm1 fm2 -> erased_src_diags fm1 = erased_src_diags fm2.
Proof.
  intro Heq. unfold erased_src_diags. rewrite (annotate_source_files_equal _ _ Heq). f_equal.
  assert (Hb : Syntax.file_bindings fm1 = Syntax.file_bindings fm2)
    by (unfold Syntax.file_bindings; apply Collections.file_elements_equal; exact Heq).
  unfold source_keyed_visit. rewrite Hb. reflexivity.
Qed.

(** two programs with the same file map produce the identical erased report *)
Theorem erased_report_files_equal (p1 p2 : Syntax.Program)
    (idx1 : Index.Snapshot.Syntax p1) (idx2 : Index.Snapshot.Syntax p2) :
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intro Heq. rewrite !erased_report_src_eq. unfold erased_report_src.
  rewrite (erased_src_diags_files_equal _ _ Heq). reflexivity.
Qed.

(** a permuted file-node list yields the identical erased report *)
Theorem erased_report_build_permutation : forall ms nodes1 nodes2 p1 p2
    (idx1 : Index.Snapshot.Syntax p1) (idx2 : Index.Snapshot.Syntax p2),
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intros ms nodes1 nodes2 p1 p2 idx1 idx2 Hperm Hb1 Hb2.
  apply erased_report_files_equal. unfold build_program in *.
  destruct (Syntax.files_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (Syntax.files_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [Syntax.files].
  exact (Syntax.files_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(* the fact table's keys and values are both source-derived, so it needs no erasure to be compared *)
Definition keyed_add (ke : Index.Key * Index.Occurrence)
    (m : Index.KeyMap.t ExpressionFact) : Index.KeyMap.t ExpressionFact :=
  match occurrence_expr_fact (snd ke) with
  | Some f => Index.KeyMap.add (fst ke) f m
  | None => m
  end.

Definition keyed_facts (l : list (Index.Key * Index.Occurrence)) : Index.KeyMap.t ExpressionFact :=
  fold_right keyed_add (Index.KeyMap.empty ExpressionFact) l.

Lemma program_expr_facts_source (p : Syntax.Program) : program_expr_facts p = keyed_facts (keyed_visit p).
Proof.
  rewrite program_expr_facts_eq_spec. unfold keyed_facts, keyed_visit.
  induction (program_visit p) as [|ro L IH]; [reflexivity|].
  cbn [map fold_right]. rewrite IH. unfold add_occ_fact, keyed_add. cbn [fst snd]. reflexivity.
Qed.

(** the expression fact table depends only on the file map *)
Lemma program_expr_facts_files_equal (p1 p2 : Syntax.Program) :
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> program_expr_facts p1 = program_expr_facts p2.
Proof.
  intro Heq. rewrite !program_expr_facts_source, (keyed_visit_files_equal p1 p2 Heq). reflexivity.
Qed.

Theorem program_expr_facts_enum_files_equal (p1 p2 : Syntax.Program) :
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) ->
  Index.KeyMap.elements (program_expr_facts p1) = Index.KeyMap.elements (program_expr_facts p2).
Proof. intro Heq. rewrite (program_expr_facts_files_equal p1 p2 Heq). reflexivity. Qed.

(** a missing-main diagnostic comes from an empty bucket and anchors at that represented package *)
Lemma package_diag_of_bucket_missing_sound {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres dir l Hmt pk :
  In (MissingMainEntry pk) (@package_diag_of_bucket p m Hpres dir l Hmt) ->
  l = nil /\ package_ref_key pk = dir.
Proof.
  intro Hin. unfold package_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. injection Heq as Hpk. subst pk. split; reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq _]]. discriminate Heq.
Qed.

(** a redeclaration comes from a bucket whose head is the first main and whose tail holds the later one *)
Lemma package_diag_of_bucket_dup_sound {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres dir l Hmt later earlier :
  In (MainRedeclared later earlier) (@package_diag_of_bucket p m Hpres dir l Hmt) ->
  exists rest, l = earlier :: rest /\ In later rest.
Proof.
  intro Hin. unfold package_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. discriminate Heq.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq Hdk]]. injection Heq as Hl He.
    exists rest. split; [ rewrite <- He; reflexivity | rewrite <- Hl; exact Hdk ].
Qed.

(* a diagnostic in the flattened bucket enumeration comes from SOME mapped bucket of [m]. *)
Lemma bucket_diags_elems_in {p} (m : PackageMap.t (list (Index.DeclRef p))) Hpres es Hall : forall d,
  In d (@bucket_diags_elems p m Hpres es Hall) ->
  exists dir l (Hmt : PackageMap.MapsTo dir l m), In d (@package_diag_of_bucket p m Hpres dir l Hmt).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems]; intros d Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exists (fst kv), (snd kv), (Hall kv (or_introl eq_refl)). exact Hin.
    + destruct (IH (fun kv' Hin' => Hall kv' (or_intror Hin')) d Hin) as [dir [l [Hmt Hd]]].
      exists dir, l, Hmt. exact Hd.
Qed.

(** a whole-program redeclaration anchors two genuine declarations in one package *)
Lemma package_diags_dup_sound {p} (idx : Index.Snapshot.Syntax p) later earlier :
  In (MainRedeclared later earlier) (package_diags idx) ->
  FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref later)))
    = FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref earlier)))
  /\ Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref later)) = Index.DeclarationKind
  /\ Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref earlier)) = Index.DeclarationKind.
Proof.
  intro Hin. unfold package_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (package_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PackageMap.find dir (program_package_refs idx) = Some l) by (apply PackageMap.find_1; exact Hmt).
  assert (HinE : In earlier l) by (rewrite Hl; left; reflexivity).
  assert (HinL : In later l)  by (rewrite Hl; right; exact Hlater).
  split; [ | split ].
  - rewrite (program_package_refs_belongs idx dir l Hfind later HinL),
            (program_package_refs_belongs idx dir l Hfind earlier HinE); reflexivity.
  - exact (Index.noderefof_kind later).
  - exact (Index.noderefof_kind earlier).
Qed.

(** a whole-program missing-main anchors a represented package that genuinely holds no main *)
Lemma package_diags_missing_sound {p} (idx : Index.Snapshot.Syntax p) pk :
  In (MissingMainEntry pk) (package_diags idx) ->
  package_present_b p (package_ref_key pk) = true
  /\ package_main_count (package_ref_key pk) (Syntax.files p) = 0%nat.
Proof.
  intro Hin. unfold package_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (package_diag_of_bucket_missing_sound _ _ dir l Hmt pk Hd) as [Hl Hkey]. subst l.
  split.
  - exact (package_ref_ok pk).
  - rewrite Hkey. symmetry. exact (program_package_refs_bucket_len idx dir nil (PackageMap.find_1 Hmt)).
Qed.

(** the buckets are key-sorted and duplicate-free, because the whole visit stream is *)
Lemma visit_file_key_sorted {p} (fr : Index.Snapshot.FileRef p) :
  StronglySorted (fun x y => Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (fst x)) (Index.Snapshot.node_ref_key (fst y)))
                 (Index.Snapshot.visit_file fr).
Proof.
  apply (strongly_sorted_impl_in (fun x y => Pos.lt (Index.Snapshot.node_ref_local (fst x)) (Index.Snapshot.node_ref_local (fst y)))).
  - intros [rx ox] [ry oy] Hx Hy Hlt.
    destruct (Index.Snapshot.visit_file_view p fr rx ox Hx) as [_ Hfx].
    destruct (Index.Snapshot.visit_file_view p fr ry oy Hy) as [_ Hfy].
    cbn [fst] in *. rewrite (Index.Snapshot.node_ref_key_eq rx), (Index.Snapshot.node_ref_key_eq ry).
    right. cbn [Index.key_path Index.key_local]. split; [ rewrite Hfx, Hfy; reflexivity | exact Hlt ].
  - apply strongly_sorted_map_inv. exact (Index.Snapshot.visit_file_order p fr).
Qed.

(* every node visited in binding [b]'s block has that binding's path as its key's file component. *)
Lemma binding_block_key_file (p : Syntax.Program) (b : FilePath.T * Syntax.File) :
  forall ro, In ro (binding_visit p b) -> Index.key_path (Index.Snapshot.node_ref_key (fst ro)) = fst b.
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  destruct (Index.Snapshot.visit_file_view p fr r occ Hin) as [_ Hf].
  cbn [fst]. rewrite (Index.Snapshot.node_ref_key_eq r). cbn [Index.key_path]. rewrite Hf.
  exact (Index.Snapshot.file_of_path_sound p (fst b) fr Efr).
Qed.

Lemma program_visit_key_sorted_aux (p : Syntax.Program) (L : list (FilePath.T * Syntax.File)) :
  StronglySorted (fun a b => Collections.FilePathOrder.lt (fst a) (fst b)) L ->
  StronglySorted (fun x y => Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (fst x)) (Index.Snapshot.node_ref_key (fst y)))
                 (concat (map (binding_visit p) L)).
Proof.
  induction L as [|b L IH]; intro Hbsort; [constructor|].
  apply StronglySorted_inv in Hbsort. destruct Hbsort as [Hbs Hbhd].
  cbn [map concat]. apply strongly_sorted_app.
  { unfold binding_visit. destruct (Index.Snapshot.file_of_path p (fst b)) as [fr|]; [apply visit_file_key_sorted | constructor]. }
  { apply IH; exact Hbs. }
  intros x y Hx Hy. apply in_concat in Hy. destruct Hy as [block [Hblock Hyb]].
  apply in_map_iff in Hblock. destruct Hblock as [b' [Hb'v Hb'L]]. subst block.
  assert (Hxf : Index.key_path (Index.Snapshot.node_ref_key (fst x)) = fst b) by (apply binding_block_key_file; exact Hx).
  assert (Hyf : Index.key_path (Index.Snapshot.node_ref_key (fst y)) = fst b') by (apply binding_block_key_file; exact Hyb).
  rewrite Forall_forall in Hbhd. pose proof (Hbhd b' Hb'L) as Hlt.
  unfold Index.KeyOrderedType.lt. left. rewrite Hxf, Hyf. exact Hlt.
Qed.

Lemma program_visit_key_sorted (p : Syntax.Program) :
  StronglySorted (fun x y => Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (fst x)) (Index.Snapshot.node_ref_key (fst y)))
                 (program_visit p).
Proof.
  unfold program_visit, program_blocks. apply program_visit_key_sorted_aux.
  apply Sorted_StronglySorted; [ intros x y z; apply Collections.FilePathOrder.lt_trans | ].
  unfold Syntax.file_bindings. apply Collections.FileMap.elements_3.
Qed.

(* one step's effect on one bucket: prepend this occurrence's reference, or leave the bucket alone *)
Lemma program_package_step_bucket {p} (idx : Index.Snapshot.Syntax p)
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence) (acc : PackageMap.t (list (Index.DeclRef p))) (dir : string) :
  (match PackageMap.find dir (program_package_step idx ro acc) with Some bk => bk | None => nil end)
  = (if String.eqb (occurrence_pkg ro) dir
     then match Index.as_decl idx (fst ro) with
          | Some dr => dr :: (match PackageMap.find dir acc with Some bk => bk | None => nil end)
          | None => (match PackageMap.find dir acc with Some bk => bk | None => nil end)
          end
     else (match PackageMap.find dir acc with Some bk => bk | None => nil end)).
Proof.
  unfold program_package_step. destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PackageFacts.add_eq_o by reflexivity. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PackageFacts.add_neq_o by exact Edir. reflexivity.
  - destruct (Index.as_kind idx (fst ro) Index.FileKind) as [fnr|] eqn:Ef.
    + destruct (PackageMap.find (occurrence_pkg ro) acc) as [l0|] eqn:Efind.
      * destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; subst dir | ]; reflexivity.
      * destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PackageFacts.add_eq_o by reflexivity.
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PackageFacts.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occurrence_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Definition bucket_of {p} (idx : Index.Snapshot.Syntax p)
    (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) (dir : string) : list (Index.DeclRef p) :=
  match PackageMap.find dir (fold_right (program_package_step idx) (PackageMap.empty _) l) with Some bk => bk | None => nil end.

(* stated over a real head symbol, so rewriting's keyed unification can find it *)
Lemma program_package_fold_bucket_cons {p} (idx : Index.Snapshot.Syntax p)
    (ro : Index.Snapshot.NodeRef p * Index.Occurrence)
    (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) (dir : string) :
  bucket_of idx (ro :: l) dir
  = (if String.eqb (occurrence_pkg ro) dir
     then match Index.as_decl idx (fst ro) with
          | Some dr => dr :: bucket_of idx l dir
          | None => bucket_of idx l dir
          end
     else bucket_of idx l dir).
Proof. unfold bucket_of. cbn [fold_right]. apply (program_package_step_bucket idx ro (fold_right (program_package_step idx) (PackageMap.empty _) l) dir). Qed.

(* over a key-sorted stream every bucket is key-sorted, and each reference erases into that stream *)
Lemma program_package_dir_sorted {p} (idx : Index.Snapshot.Syntax p) (l : list (Index.Snapshot.NodeRef p * Index.Occurrence)) :
  StronglySorted (fun x y => Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (fst x)) (Index.Snapshot.node_ref_key (fst y))) l ->
  forall dir,
    StronglySorted (fun a b => Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (Index.erase_ref a))
                                                     (Index.Snapshot.node_ref_key (Index.erase_ref b))) (bucket_of idx l dir)
    /\ (forall a, In a (bucket_of idx l dir) -> exists ro, In ro l /\ Index.erase_ref a = fst ro).
Proof.
  induction l as [|ro l IH]; intro Hsort; intro dir.
  - unfold bucket_of. rewrite PackageFacts.empty_o. split; [constructor | intros a []].
  - apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
    specialize (IH Hsort0). destruct (IH dir) as [IHsort IHref]. split.
    + (* the bucket stays Index.Key-sorted *)
      rewrite (program_package_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occurrence_pkg ro) dir) eqn:Ek; [ destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed | ]; try exact IHsort.
      (* prepend this file's main ref — smaller key than every later main (stream sorted) *)
      assert (Her : Index.erase_ref dr = fst ro) by exact (Index.erase_as_kind idx (fst ro) Index.DeclarationKind dr Ed).
      constructor; [ exact IHsort |].
      rewrite Forall_forall. intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]].
      rewrite Forall_forall in Hhd. rewrite Her, Hae. exact (Hhd ro' Hro').
    + (* every bucket ref erases to a stream occurrence *)
      rewrite (program_package_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occurrence_pkg ro) dir) eqn:Ek; [ destruct (Index.as_decl idx (fst ro)) as [dr|] eqn:Ed | ].
      * assert (Her : Index.erase_ref dr = fst ro) by exact (Index.erase_as_kind idx (fst ro) Index.DeclarationKind dr Ed).
        intros a [Hah | Hat].
        -- subst a. exists ro. split; [left; reflexivity | exact Her].
        -- destruct (IHref a Hat) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
Qed.
(** each bucket is a strictly ascending subselection, so the related main strictly precedes the primary *)
Lemma package_diags_dup_precedence {p} (idx : Index.Snapshot.Syntax p) later earlier :
  In (MainRedeclared later earlier) (package_diags idx) ->
  Index.KeyOrderedType.lt (Index.Snapshot.node_ref_key (Index.erase_ref earlier))
                        (Index.Snapshot.node_ref_key (Index.erase_ref later))
  /\ earlier <> later.
Proof.
  intro Hin. unfold package_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (package_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PackageMap.find dir (program_package_refs idx) = Some l) by (apply PackageMap.find_1; exact Hmt).
  assert (Hbeq : bucket_of idx (program_visit p) dir = l).
  { unfold bucket_of. unfold program_package_refs, program_package_refs_from_visit in Hfind. rewrite Hfind. reflexivity. }
  destruct (program_package_dir_sorted idx (program_visit p) (program_visit_key_sorted p) dir) as [Hsort _].
  rewrite Hbeq, Hl in Hsort. apply StronglySorted_inv in Hsort. destruct Hsort as [_ Hhd].
  rewrite Forall_forall in Hhd. pose proof (Hhd later Hlater) as Hlt.
  split; [ exact Hlt |].
  intro Heq. subst later.
  assert (Hne : ~ Index.KeyOrderedType.eq (Index.Snapshot.node_ref_key (Index.erase_ref earlier))
                                        (Index.Snapshot.node_ref_key (Index.erase_ref earlier)))
    by (apply Index.KeyOrderedType.lt_not_eq; exact Hlt).
  apply Hne. apply (proj2 (Index.key_compare_equal _ _)). reflexivity.
Qed.

(** the node-anchored report is strictly ascending by key, with no project-authored sort *)
Definition key_lt_opt (oa ob : option Index.Key) : Prop :=
  match oa, ob with Some ka, Some kb => Index.KeyOrderedType.lt ka kb | _, _ => False end.

Lemma key_lt_irreflexive : forall a, ~ Index.KeyOrderedType.lt a a.
Proof.
  intros a H. assert (Hne : ~ Index.KeyOrderedType.eq a a) by (apply Index.KeyOrderedType.lt_not_eq; exact H).
  apply Hne. apply (proj2 (Index.key_compare_equal a a)). reflexivity.
Qed.

Lemma package_map_elements_no_duplicates_fst {A} (m : PackageMap.t A) : NoDup (map fst (PackageMap.elements m)).
Proof.
  pose proof (PackageMap.elements_3w m) as H. generalize dependent (PackageMap.elements m). intro l.
  induction l as [|[k e] l IH]; simpl; intro H; [constructor|].
  inversion H as [|x xs Hni Hnd Heq]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' e'] [Hk Hin']]. cbn in Hk; subst k'.
    apply Hni, SetoidList.InA_alt. exists (k, e'). split; [ reflexivity | exact Hin' ].
  - apply IH; exact Hnd.
Qed.

(* NoDup of a disjoint append (stdlib has no direct form). *)
Lemma no_duplicates_app_disjoint {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  intros H1 H2 Hd. induction l1 as [|a l1 IH]; [exact H2|].
  cbn [app]. apply NoDup_cons_iff in H1. destruct H1 as [Hni H1].
  apply NoDup_cons_iff. split.
  - intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + exact (Hni Hin).
    + exact (Hd a (or_introl eq_refl) Hin).
  - apply IH; [exact H1 | intros x Hx1 Hx2; exact (Hd x (or_intror Hx1) Hx2)].
Qed.

(* every key of the folded bucket map is one of the input keys. *)
Lemma bucket_find_in_keys {X} (kxs : list (Index.Key * X)) (k : Index.Key) (b : list X) :
  Index.KeyMap.MapsTo k b (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs) ->
  In k (map fst kxs).
Proof.
  induction kxs as [|kx rest IH]; cbn [fold_right map].
  - intro Hmt. apply Index.KeyFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - unfold bucket_add. intro Hmt. apply Index.KeyFacts.add_mapsto_iff in Hmt.
    destruct Hmt as [[Hk _]|[_ Hmt]].
    + unfold Index.KeyOrderedType.eq in Hk. subst k. left; reflexivity.
    + right. exact (IH Hmt).
Qed.

(* unique input keys => every bucket is a singleton. *)
Lemma nodup_keys_buckets_singleton {X} (kxs : list (Index.Key * X)) :
  NoDup (map fst kxs) ->
  forall k b, Index.KeyMap.MapsTo k b (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs) ->
  length b = 1%nat.
Proof.
  induction kxs as [|kx rest IH]; intros Hnd k b Hmt.
  - cbn [fold_right] in Hmt. apply Index.KeyFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd].
    cbn [fold_right] in Hmt.
    set (M := fold_right bucket_add (Index.KeyMap.empty (list X)) rest) in *.
    unfold bucket_add in Hmt.
    apply Index.KeyFacts.add_mapsto_iff in Hmt. destruct Hmt as [[Hk Hb]|[_ Hmt]].
    + subst b. unfold Index.KeyOrderedType.eq in Hk. subst k.
      assert (Hnf : nkm_find (fst kx) M = []).
      { unfold nkm_find. destruct (Index.KeyMap.find (fst kx) M) as [b'|] eqn:Ef; [|reflexivity].
        exfalso. apply Hni. apply Index.KeyFacts.find_mapsto_iff in Ef.
        exact (bucket_find_in_keys rest (fst kx) b' Ef). }
      rewrite Hnf. reflexivity.
    + exact (IH Hnd k b Hmt).
Qed.

(* singleton buckets, key-sorted elements => the flattening is STRICTLY key-ascending. *)
Lemma flat_map_snd_bucket_singleton_strict {X} (key : X -> option Index.Key)
    (els : list (Index.Key * list X)) :
  Sorted (@Index.KeyMap.lt_key (list X)) els ->
  (forall k b, In (k, b) els -> forall d, In d b -> key d = Some k) ->
  (forall k b, In (k, b) els -> length b = 1%nat) ->
  StronglySorted (fun a b => key_lt_opt (key a) (key b)) (flat_map snd els).
Proof.
  induction els as [|[k b] rest IH]; intro Hs; intros Hkey Hlen; cbn [flat_map snd]; [constructor|].
  pose proof (Sorted_StronglySorted nkmap_lt_key_trans Hs) as Hss.
  apply StronglySorted_inv in Hss. destruct Hss as [_ Hhd]. apply Sorted_inv in Hs. destruct Hs as [Hs _].
  assert (Hb1 : length b = 1%nat) by exact (Hlen k b (or_introl eq_refl)).
  destruct b as [|d [|d' b']]; cbn [length] in Hb1; try discriminate Hb1.
  cbn [app]. constructor.
  - apply IH; [ exact Hs
    | intros k' b0 Hin' d0 Hd0; exact (Hkey k' b0 (or_intror Hin') d0 Hd0)
    | intros k' b0 Hin'; exact (Hlen k' b0 (or_intror Hin')) ].
  - rewrite Forall_forall. intros a'' Ha''.
    assert (Hkd : key d = Some k) by exact (Hkey k [d] (or_introl eq_refl) d (or_introl eq_refl)).
    apply in_flat_map in Ha''. destruct Ha'' as [[k'' b''] [Hin'' Ha'']]. cbn [snd] in Ha''.
    assert (Hkd'' : key a'' = Some k'') by exact (Hkey k'' b'' (or_intror Hin'') a'' Ha'').
    unfold key_lt_opt. rewrite Hkd, Hkd''.
    rewrite Forall_forall in Hhd. exact (Hhd (k'', b'') Hin'').
Qed.

Lemma bucket_flatten_singleton_strict {X} (key : X -> option Index.Key) (kxs : list (Index.Key * X))
    (Hself : forall kd, In kd kxs -> key (snd kd) = Some (fst kd))
    (Hsingle : forall k b, Index.KeyMap.MapsTo k b
                 (fold_right bucket_add (Index.KeyMap.empty (list X)) kxs) -> length b = 1%nat) :
  StronglySorted (fun a b => key_lt_opt (key a) (key b)) (bucket_flatten kxs).
Proof.
  unfold bucket_flatten. apply flat_map_snd_bucket_singleton_strict.
  - apply Index.KeyMap.elements_3.
  - intros k b Hin d Hd. apply (bucket_value_key key kxs Hself k b); [
      apply Index.KeyFacts.elements_mapsto_iff, InA_alt; exists (k, b);
        split; [split; reflexivity | exact Hin] | exact Hd ].
  - intros k b Hin. apply (Hsingle k b).
    apply Index.KeyFacts.elements_mapsto_iff, InA_alt. exists (k, b);
      split; [split; reflexivity | exact Hin].
Qed.

(* the tail duplicate-main keys of one package bucket are NoDup (the bucket is a strictly-sorted visit stream). *)
Lemma bucket_dup_keys_nodup {p} (idx : Index.Snapshot.Syntax p) (kv : string * list (Index.DeclRef p)) :
  PackageMap.find (fst kv) (program_package_refs idx) = Some (snd kv) -> NoDup (bucket_dup_keys (snd kv)).
Proof.
  intro Hfind.
  destruct (program_package_dir_sorted idx (program_visit p) (program_visit_key_sorted p) (fst kv)) as [Hsort _].
  assert (Hb : bucket_of idx (program_visit p) (fst kv) = snd kv)
    by (unfold bucket_of; unfold program_package_refs, program_package_refs_from_visit in Hfind; rewrite Hfind; reflexivity).
  rewrite Hb in Hsort. destruct (snd kv) as [|d1 rest]; cbn [bucket_dup_keys]; [constructor|].
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort _].
  apply (strongly_sorted_no_duplicates Index.KeyOrderedType.lt); [ exact key_lt_irreflexive |].
  apply (strongly_sorted_map Index.KeyOrderedType.lt (fun dk => Index.Snapshot.node_ref_key (Index.erase_ref dk))).
  exact Hsort.
Qed.

Lemma package_node_keys_nodup {p} (idx : Index.Snapshot.Syntax p) : NoDup (node_keys (package_diags idx)).
Proof.
  rewrite package_node_keys_spec.
  apply (nodup_flat_map_tag (fun kv => bucket_dup_keys (snd kv))
           (fun k => FilePath.parent (Index.key_path k)) (fun kv => fst kv)).
  - intros kv Hin. apply (bucket_dup_keys_nodup idx kv).
    apply PackageMap.find_1, PackageFacts.elements_mapsto_iff, InA_alt. exists kv. split; [split; reflexivity | exact Hin].
  - intros kv k Hin Hk.
    assert (Hfind : PackageMap.find (fst kv) (program_package_refs idx) = Some (snd kv))
      by (apply PackageMap.find_1, PackageFacts.elements_mapsto_iff, InA_alt; exists kv; split; [split; reflexivity | exact Hin]).
    unfold bucket_dup_keys in Hk. destruct (snd kv) as [|d1 rest] eqn:Esnd; [destruct Hk|].
    apply in_map_iff in Hk. destruct Hk as [dk [Hdk Hdkin]].
    rewrite <- Hdk, Index.Snapshot.node_ref_key_eq. cbn [Index.key_path].
    apply (program_package_refs_belongs idx (fst kv) (d1 :: rest)); [ exact Hfind | right; exact Hdkin ].
  - apply package_map_elements_no_duplicates_fst.
Qed.

(* an expression key and a declaration key are never the same occurrence, so the two key sets are disjoint *)
Lemma occurrence_expr_diags_key_kind {p} (idx : Index.Snapshot.Syntax p) outer ro :
  forall d, In d (occurrence_expr_diags idx outer ro) ->
  diag_node_key d = Some (Index.Snapshot.node_ref_key (fst ro)) /\
  Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (fst ro)) = Index.ExpressionKind.
Proof.
  intros d Hin. unfold occurrence_expr_diags in Hin.
  destruct (Index.as_expr idx (fst ro)) as [er|] eqn:Ea; [|destruct Hin].
  assert (Her : Index.erase_ref er = fst ro) by exact (Index.erase_as_kind idx (fst ro) Index.ExpressionKind er Ea).
  assert (Hk : Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (fst ro)) = Index.ExpressionKind)
    by (rewrite <- Her; exact (Index.noderefof_kind er)).
  destruct (Index.view_expr (snd ro)) as [e|]; [|destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct (conversion_target_ref idx er) as [tr|]; [|destruct Hin].
    destruct (conversion_operand_ref idx er) as [opr|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]].
    split; [ cbn [diag_node_key diagnostic_primary]; rewrite Her; reflexivity | exact Hk ].
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]].
    split; [ cbn [diag_node_key diagnostic_primary]; rewrite Her; reflexivity | exact Hk ].
Qed.

Lemma expression_node_key_has_kind {p} (idx : Index.Snapshot.Syntax p) :
  forall k, In k (node_keys (expression_diags idx)) ->
  exists r : Index.Snapshot.NodeRef p,
    Index.Snapshot.node_ref_key r = k /\
    Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref r) = Index.ExpressionKind.
Proof.
  intros k Hin. unfold node_keys in Hin. apply in_flat_map in Hin. destruct Hin as [d [Hd Hk]].
  destruct (diag_node_key d) as [k0|] eqn:Edk; cbn [In] in Hk; [|destruct Hk].
  destruct Hk as [Heq|[]]. subst k0.
  rewrite expression_diags_eq_spec in Hd. apply in_flat_map in Hd. destruct Hd as [roc [_ Hd]].
  destruct (occurrence_expr_diags_key_kind idx (snd roc) (fst roc) d Hd) as [Hdk2 Hkind].
  rewrite Edk in Hdk2. injection Hdk2 as Hkk.
  exists (fst (fst roc)). split; [ exact (eq_sym Hkk) | exact Hkind ].
Qed.

Lemma package_node_key_has_kind {p} (idx : Index.Snapshot.Syntax p) :
  forall k, In k (node_keys (package_diags idx)) ->
  exists r : Index.Snapshot.NodeRef p,
    Index.Snapshot.node_ref_key r = k /\
    Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref r) = Index.DeclarationKind.
Proof.
  intros k Hin. rewrite package_node_keys_spec in Hin.
  apply in_flat_map in Hin. destruct Hin as [kv [_ Hin]].
  unfold bucket_dup_keys in Hin. destruct (snd kv) as [|d1 rest]; [destruct Hin|].
  apply in_map_iff in Hin. destruct Hin as [dk [Hdk _]].
  exists (Index.erase_ref dk). split; [ exact Hdk | exact (Index.noderefof_kind dk) ].
Qed.

Lemma expression_pkg_node_keys_disjoint {p} (idx : Index.Snapshot.Syntax p) :
  forall k, In k (node_keys (expression_diags idx)) -> In k (node_keys (package_diags idx)) -> False.
Proof.
  intros k He Hp.
  destruct (expression_node_key_has_kind idx k He) as [re [Hre Hke]].
  destruct (package_node_key_has_kind idx k Hp) as [rd [Hrd Hkd]].
  assert (Hreq : re = rd) by (apply Index.Snapshot.node_ref_key_inj; rewrite Hre, Hrd; reflexivity).
  subst rd. rewrite Hke in Hkd. discriminate Hkd.
Qed.

(** the node-keyed diagnostic INPUT has UNIQUE keys (expr NoDup + pkg NoDup + disjoint). *)
Theorem collect_node_input_nodup {p} (idx : Index.Snapshot.Syntax p) :
  NoDup (node_keys (expression_diags idx ++ package_diags idx)).
Proof.
  rewrite node_keys_app. apply no_duplicates_app_disjoint;
    [ apply expression_node_keys_nodup | apply package_node_keys_nodup | apply expression_pkg_node_keys_disjoint ].
Qed.

(** every node-keyed diagnostic BUCKET is a SINGLETON (from the unique input keys). *)
Theorem collect_node_buckets_singleton {p} (idx : Index.Snapshot.Syntax p) :
  forall k b, Index.KeyMap.MapsTo k b
    (fold_right bucket_add (Index.KeyMap.empty (list (DiagnosticReason p)))
       (node_keyed (expression_diags idx ++ package_diags idx))) -> length b = 1%nat.
Proof.
  apply nodup_keys_buckets_singleton. rewrite node_keys_eq. apply collect_node_input_nodup.
Qed.

(** the map flattening is the canonical enumeration, and unique keys leave no ties *)
Theorem semantic_diagnostics_node_strict {p} (idx : Index.Snapshot.Syntax p) :
  StronglySorted (fun a b => key_lt_opt (diag_node_key a) (diag_node_key b))
                 (bucket_flatten (node_keyed (expression_diags idx ++ package_diags idx))).
Proof.
  apply bucket_flatten_singleton_strict; [ apply node_keyed_self | apply collect_node_buckets_singleton ].
Qed.

(** the default-output-name layer, faithful to the pinned toolchain's own two functions *)

Local Open Scope string_scope.

Definition ascii_is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 48 n) (Nat.leb n 57).

(* every byte of [s] is a decimal digit. *)
Fixpoint str_all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => andb (ascii_is_digit c) (str_all_digits s')
  end.

(* a version element, as one conjunction rather than a branch, for a clean reflection *)
Definition is_version_element (s : string) : bool :=
  match s with
  | String c0 (String c1 rest) =>
      andb (Ascii.eqb c0 "v"%char)
        (andb (negb (Ascii.eqb c1 "0"%char))
          (andb (negb (andb (Ascii.eqb c1 "1"%char)
                            (match rest with EmptyString => true | _ => false end)))
                (str_all_digits (String c1 rest))))
  | _ => false
  end.

(* the last component, dropped to the previous one exactly when it is a version element *)
Definition default_exec_name_c (comps : list string) : string :=
  match comps with
  | _ :: _ :: _ =>
      let final := List.last comps ""%string in
      if is_version_element final then List.last (List.removelast comps) ""%string else final
  | _ => List.last comps ""%string
  end.

(** reflection — [is_version_element] agrees with the pinned structural predicate. *)
Lemma is_version_element_spec : forall s,
  is_version_element s = true <->
  (exists c1 rest, s = String "v"%char (String c1 rest)
                   /\ c1 <> "0"%char
                   /\ ~ (c1 = "1"%char /\ rest = EmptyString)
                   /\ str_all_digits (String c1 rest) = true).
Proof.
  intros s. split.
  - destruct s as [|c0 [|c1 rest]]; cbn [is_version_element]; try discriminate.
    intro H.
    apply andb_true_iff in H; destruct H as [Hv H].
    apply andb_true_iff in H; destruct H as [H0 H].
    apply andb_true_iff in H; destruct H as [H1 Hd].
    apply Ascii.eqb_eq in Hv; subst c0.
    exists c1, rest. split; [reflexivity | split; [ | split ] ].
    + apply negb_true_iff, Ascii.eqb_neq in H0. exact H0.
    + apply negb_true_iff, andb_false_iff in H1. intros [Hc1 Hre]. destruct H1 as [H1|H1].
      * apply Ascii.eqb_neq in H1. exact (H1 Hc1).
      * subst rest. cbn in H1. discriminate H1.
    + exact Hd.
  - intros [c1 [rest [Hs [H0 [H1 Hd]]]]]. subst s. cbn [is_version_element].
    apply andb_true_iff; split; [ apply Ascii.eqb_refl |].
    apply andb_true_iff; split.
    + apply negb_true_iff. apply Ascii.eqb_neq. exact H0.
    + apply andb_true_iff; split; [ | exact Hd ].
      apply negb_true_iff, andb_false_iff.
      destruct (Ascii.eqb c1 "1"%char) eqn:E1; [ | left; reflexivity ].
      apply Ascii.eqb_eq in E1. subst c1. right. destruct rest as [|rc rr].
      * exfalso. apply H1. split; reflexivity.
      * reflexivity.
Qed.

(** the version-element fixtures, against the pinned toolchain *)
Example version_suffix_v0   : is_version_element "v0"   = false. Proof. reflexivity. Qed.
Example version_suffix_v00  : is_version_element "v00"  = false. Proof. reflexivity. Qed.
Example version_suffix_v01  : is_version_element "v01"  = false. Proof. reflexivity. Qed.
Example version_suffix_v05  : is_version_element "v05"  = false. Proof. reflexivity. Qed.
Example version_suffix_v1   : is_version_element "v1"   = false. Proof. reflexivity. Qed.
Example version_suffix_lowercase_accepted   : is_version_element "v2"   = true.  Proof. reflexivity. Qed.
Example version_suffix_v3   : is_version_element "v3"   = true.  Proof. reflexivity. Qed.
Example version_suffix_v10  : is_version_element "v10"  = true.  Proof. reflexivity. Qed.
Example version_suffix_v100 : is_version_element "v100" = true.  Proof. reflexivity. Qed.
Example version_suffix_v1x  : is_version_element "v1x"  = false. Proof. reflexivity. Qed.
Example version_suffix_v2x  : is_version_element "v2x"  = false. Proof. reflexivity. Qed.
Example version_suffix_uppercase_rejected   : is_version_element "V2"   = false. Proof. reflexivity. Qed.
Example version_suffix_v    : is_version_element "v"    = false. Proof. reflexivity. Qed.

(** default_exec_name_c FIXTURES — the exact pinned import-path COMPONENTS -> exe-name rule. *)
Example den_root    : default_exec_name_c ["example.com"; "m"]               = "m".       Proof. reflexivity. Qed.
Example den_sub     : default_exec_name_c ["example.com"; "m"; "sub"]        = "sub".     Proof. reflexivity. Qed.
Example den_ab      : default_exec_name_c ["example.com"; "m"; "a"; "b"]     = "b".       Proof. reflexivity. Qed.
Example den_av2     : default_exec_name_c ["example.com"; "m"; "a"; "v2"]    = "a".       Proof. reflexivity. Qed.
Example den_v2      : default_exec_name_c ["example.com"; "m"; "v2"]         = "m".       Proof. reflexivity. Qed.
Example den_maingo  : default_exec_name_c ["example.com"; "main.go"]         = "main.go". Proof. reflexivity. Qed.
Example den_gomod   : default_exec_name_c ["example.com"; "go.mod"]          = "go.mod".  Proof. reflexivity. Qed.
Example den_sub_v10 : default_exec_name_c ["example.com"; "m"; "sub"; "v10"] = "sub".     Proof. reflexivity. Qed.

(** the import path and default executable name, composed from the lower-layer component authorities *)
Definition package_import_components (ms : ModuleSpec) (dir : string) : list string :=
  ModulePath.segments (module_path ms) ++ FilePath.dir_components dir.

(* the default executable name: cmd/go's rule DIRECTLY over the import-path components (no reparse). *)
Definition default_exec_name (ms : ModuleSpec) (dir : string) : string :=
  default_exec_name_c (package_import_components ms dir).

(* the exact cmd/go import-path STRING: the "/"-join of the components (the ONE string bridge/view). *)
Definition package_import_path (ms : ModuleSpec) (dir : string) : string :=
  String.concat "/" (package_import_components ms dir).

(* generic "/"-join shape helpers (list-of-string; no character scan). *)
Lemma sapp_assoc : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. intros a b c. induction a as [|x a' IH]; [ reflexivity | cbn [append]; rewrite IH; reflexivity ]. Qed.

Lemma concat_cons2 : forall sep x y rest,
  String.concat sep (x :: y :: rest) = (x ++ sep ++ String.concat sep (y :: rest))%string.
Proof. intros sep x y rest. reflexivity. Qed.

(* the "/"-join of the concatenation of two NONEMPTY component lists splits at the join. *)
Lemma concat_app_join : forall (A B : list string), A <> [] -> B <> [] ->
  String.concat "/" (A ++ B) = (String.concat "/" A ++ "/" ++ String.concat "/" B)%string.
Proof.
  intros A. induction A as [|a A' IH]; intros B HA HB; [ contradiction |].
  destruct A' as [|a2 A''].
  - cbn [app]. destruct B as [|b B']; [ contradiction | reflexivity ].
  - cbn [app].
    rewrite (concat_cons2 "/"%string a a2 (A'' ++ B)).
    rewrite app_comm_cons.
    rewrite (IH B ltac:(discriminate) HB).
    rewrite (concat_cons2 "/"%string a a2 A'').
    rewrite <- !sapp_assoc. reflexivity.
Qed.

(* the ONE string bridge: the root key "" imports as the module path; a nested key appends "/" then the dir. *)
Lemma package_import_path_root : forall ms, package_import_path ms "" = ModulePath.text (module_path ms).
Proof.
  intro ms. unfold package_import_path, package_import_components.
  cbn [FilePath.dir_components String.eqb]. rewrite app_nil_r, ModulePath.text_concat. reflexivity.
Qed.

Lemma package_import_path_nested : forall ms dir, dir <> ""%string ->
  package_import_path ms dir = (ModulePath.text (module_path ms) ++ "/" ++ dir)%string.
Proof.
  intros ms dir Hd. unfold package_import_path, package_import_components, FilePath.dir_components.
  destruct (String.eqb dir ""%string) eqn:E; [ apply String.eqb_eq in E; contradiction |].
  rewrite (concat_app_join _ _ (ModulePath.segments_nonempty (module_path ms))
                               (FilePath.split_slash_nonempty dir)).
  rewrite ModulePath.text_concat, FilePath.split_slash_concat. reflexivity.
Qed.

(* the component list is nonempty (the module always has >= 1 segment). *)
Lemma package_import_components_nonempty : forall ms dir, package_import_components ms dir <> [].
Proof.
  intros ms dir. unfold package_import_components. intro Hc.
  apply (ModulePath.segments_nonempty (module_path ms)).
  destruct (ModulePath.segments (module_path ms)); [ reflexivity | discriminate Hc ].
Qed.

Lemma last_in : forall (l : list string), l <> [] -> In (List.last l ""%string) l.
Proof.
  induction l as [|x l IH]; intro H; [ contradiction |].
  destruct l as [|y l']; [ left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma removelast_in : forall (l : list string) x, In x (List.removelast l) -> In x l.
Proof.
  induction l as [|a l IH]; intros x Hin.
  - cbn [List.removelast] in Hin. exact Hin.
  - destruct l as [|b l'].
    + cbn [List.removelast] in Hin. destruct Hin.
    + cbn [List.removelast] in Hin. destruct Hin as [->|Hin]; [ left; reflexivity | right; apply IH; exact Hin ].
Qed.

(* the exec name IS one of the components (the last, or the previous when the last is a version element). *)
Lemma default_exec_name_c_in : forall comps, comps <> [] -> In (default_exec_name_c comps) comps.
Proof.
  intros comps Hne. unfold default_exec_name_c. destruct comps as [|a [|b rest]]; [ contradiction | |].
  - cbn [List.last]. left; reflexivity.
  - destruct (is_version_element (List.last (a :: b :: rest) ""%string)).
    + apply removelast_in, last_in. cbn [List.removelast]. discriminate.
    + apply last_in. discriminate.
Qed.

(** the default executable name is never empty, because every component it can be is nonempty *)
Lemma default_exec_name_nonempty : forall ms dir,
  (dir = ""%string \/ exists fp, FilePath.parent fp = dir) ->
  default_exec_name ms dir <> ""%string.
Proof.
  intros ms dir Hdir. unfold default_exec_name.
  assert (Hall : forall s, In s (package_import_components ms dir) -> s <> ""%string).
  { intros s Hs. unfold package_import_components in Hs. apply in_app_or in Hs. destruct Hs as [Hs|Hs].
    - exact (ModulePath.segments_nonempty_elt (module_path ms) s Hs).
    - destruct Hdir as [Hd0 | [fp Hfp]].
      + subst dir. unfold FilePath.dir_components in Hs. cbn [String.eqb] in Hs. destruct Hs.
      + apply (FilePath.parent_dir_components_nonempty fp s). rewrite Hfp. exact Hs. }
  apply Hall. apply default_exec_name_c_in. apply package_import_components_nonempty.
Qed.

(* splitting the joined import path at the module boundary recovers the directory components *)
Lemma split_import_path_dir_components : forall ms dir,
  FilePath.split_slash (package_import_path ms dir)
    = (FilePath.split_slash (ModulePath.text (module_path ms)) ++ FilePath.dir_components dir)%list.
Proof.
  intros ms dir. destruct (String.eqb dir ""%string) eqn:E.
  - apply String.eqb_eq in E; subst dir.
    rewrite package_import_path_root. unfold FilePath.dir_components.
    cbn [String.eqb]. rewrite app_nil_r. reflexivity.
  - assert (Hne : dir <> ""%string) by (apply String.eqb_neq; exact E).
    rewrite (package_import_path_nested ms dir Hne). unfold FilePath.dir_components. rewrite E.
    change ((ModulePath.text (module_path ms) ++ "/" ++ dir)%string)
      with ((ModulePath.text (module_path ms) ++ String "/"%char dir)%string).
    apply FilePath.split_slash_app.
Qed.

(* a short list-app left cancellation over string components (a leaf fact; not a collection algorithm). *)
Lemma slist_app_inv_head : forall (l l1 l2 : list string), (l ++ l1)%list = (l ++ l2)%list -> l1 = l2.
Proof.
  induction l as [|x l IH]; intros l1 l2 H; [ exact H |].
  cbn [app] in H. injection H as H. apply IH. exact H.
Qed.

(** the import path is injective in the package directory under a fixed module *)
Theorem package_import_path_inj : forall ms dir1 dir2,
  package_import_path ms dir1 = package_import_path ms dir2 -> dir1 = dir2.
Proof.
  intros ms dir1 dir2 H.
  assert (Hd : FilePath.dir_components dir1 = FilePath.dir_components dir2).
  { pose proof (split_import_path_dir_components ms dir1) as S1.
    pose proof (split_import_path_dir_components ms dir2) as S2.
    rewrite H in S1. rewrite S1 in S2. apply slist_app_inv_head in S2. exact S2. }
  pose proof (FilePath.dir_components_concat dir1) as C1.
  rewrite Hd, (FilePath.dir_components_concat dir2) in C1. exact (eq_sym C1).
Qed.

(** an equal module spec and directory key give the same import path *)
Theorem package_import_path_deterministic : forall ms1 ms2 dir1 dir2,
  ms1 = ms2 -> dir1 = dir2 -> package_import_path ms1 dir1 = package_import_path ms2 dir2.
Proof. intros ms1 ms2 dir1 dir2 Hm Hd; subst; reflexivity. Qed.

(** the pattern selects exactly the domain of the one-pass package map *)

Definition selected_packages (p : Syntax.Program) : PackageMap.t PackageSummary := package_summaries (Syntax.files p).
Definition selected_package_keys (p : Syntax.Program) : list string := map fst (PackageMap.elements (selected_packages p)).
Definition selected_package_count (p : Syntax.Program) : nat := length (selected_package_keys p).

(** domain exactness: a directory is a selected package IFF some represented file has that parent dir. *)
Lemma selected_iff_file : forall p dir,
  PackageMap.In dir (selected_packages p) <->
  (exists b, In b (Syntax.file_bindings (Syntax.files p)) /\ FilePath.parent (fst b) = dir).
Proof.
  intros p dir. unfold selected_packages. split.
  - apply package_no_empty.
  - intros [b [Hin Heq]].
    assert (Hmem : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true).
    { unfold list_dir_mem. apply existsb_exists. exists b. split; [ exact Hin | rewrite Heq; apply String.eqb_refl ]. }
    exists (MakePackageSummary (package_main_count dir (Syntax.files p))).
    apply PackageFacts.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity.
Qed.

(** the empty program selects ZERO packages. *)
Lemma selected_count_empty : forall ms, selected_package_count (empty_program ms) = 0%nat.
Proof.
  intro ms. unfold selected_package_count, selected_package_keys, selected_packages.
  assert (He : PackageMap.Empty (package_summaries (Syntax.files (empty_program ms)))).
  { intros k e Hmt. apply PackageFacts.find_mapsto_iff in Hmt.
    cbn [Syntax.files empty_program] in Hmt. rewrite (package_summaries_empty k) in Hmt. discriminate. }
  rewrite (proj1 (PackageProperties.elements_Empty _) He). reflexivity.
Qed.

(** two files sharing a parent land on one selected package key *)
Lemma selected_one_dir : forall p b1 b2,
  In b1 (Syntax.file_bindings (Syntax.files p)) -> In b2 (Syntax.file_bindings (Syntax.files p)) ->
  FilePath.parent (fst b1) = FilePath.parent (fst b2) ->
  PackageMap.In (FilePath.parent (fst b1)) (selected_packages p).
Proof.
  intros p b1 b2 Hin1 _ _. apply selected_iff_file. exists b1. split; [ exact Hin1 | reflexivity ].
Qed.

(** the fresh root layout: the go.mod, each root-level file, and one directory per nested first component *)

Inductive FreshRootEntryKind : Type :=
| GoModuleEntry
| SourceFileEntry (path : FilePath.T)
| DirectoryEntry.

(* the FIRST path component of a path string (before the first '/'); the whole name for a root-level file. *)
Fixpoint first_component (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if Ascii.eqb c "/"%char then EmptyString else String c (first_component s')
  end.

Fixpoint contains_dot (s : string) : bool :=
  match s with EmptyString => false | String c s' => orb (Ascii.eqb c "."%char) (contains_dot s') end.

Lemma contains_dot_app : forall a b, contains_dot (a ++ b) = orb (contains_dot a) (contains_dot b).
Proof. induction a as [|c a IH]; intro b; simpl; [reflexivity | rewrite IH; apply Bool.orb_assoc]. Qed.

(* a lowercase-or-digit byte is never '.'; a lowercase byte is never '.'. *)
Lemma is_lower_digit_no_dot : forall c, FilePath.is_lower_digit c = true -> Ascii.eqb c "."%char = false.
Proof.
  intros c H. apply Bool.not_true_iff_false. intro E. apply Ascii.eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

Lemma tail_ok_no_dot : forall s, FilePath.tail_ok s = true -> contains_dot s = false.
Proof.
  induction s as [|c s' IH]; intro H; [reflexivity|].
  cbn [FilePath.tail_ok] in H. apply andb_true_iff in H. destruct H as [Hc Hs].
  cbn [contains_dot]. rewrite (is_lower_digit_no_dot c Hc); cbn [orb]. exact (IH Hs).
Qed.

Lemma component_ok_no_dot : forall s, FilePath.component_ok s = true -> contains_dot s = false.
Proof.
  intros [|c s'] H; [discriminate H|].
  cbn [FilePath.component_ok] in H. apply andb_true_iff in H. destruct H as [Hc Hs].
  cbn [contains_dot].
  assert (Hne : Ascii.eqb c "."%char = false).
  { apply Bool.not_true_iff_false. intro E. apply Ascii.eqb_eq in E. subst c. vm_compute in Hc. discriminate Hc. }
  rewrite Hne; cbn [orb]. exact (tail_ok_no_dot s' Hs).
Qed.

(* a dot-free directory key can never equal the DOTTED module file name "go.mod". *)
Lemma dir_component_neq_gomod : forall d, FilePath.dir_component_ok d = true -> d <> "go.mod".
Proof.
  intros d Hd Heq. subst d. unfold FilePath.dir_component_ok in Hd. apply andb_true_iff in Hd. destruct Hd as [Hc _].
  pose proof (component_ok_no_dot _ Hc) as Hnd. vm_compute in Hnd. discriminate Hnd.
Qed.

(** a root source basename is dotted, so it can never equal a dot-free directory key *)

Lemma substring_full : forall s, String.substring 0 (String.length s) s = s.
Proof. induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma substring_split : forall k s, (k <= String.length s)%nat ->
  s = (String.substring 0 k s ++ String.substring k (String.length s - k) s)%string.
Proof.
  intros k s; revert k; induction s as [|c s IH]; intros [|k'] Hk.
  - reflexivity.
  - simpl in Hk; lia.
  - change (String.substring 0 0 (String c s)) with EmptyString.
    rewrite Nat.sub_0_r, substring_full. reflexivity.
  - cbn [String.substring String.length Nat.sub String.append]. f_equal. apply IH. simpl in Hk; lia.
Qed.

Lemma ends_go_recon : forall s, FilePath.ends_go s = true -> s = (FilePath.strip_go s ++ ".go")%string.
Proof.
  intros s H. unfold FilePath.ends_go in H. apply andb_true_iff in H. destruct H as [Hn Heq].
  apply Nat.leb_le in Hn. apply String.eqb_eq in Heq. unfold FilePath.strip_go.
  pose proof (substring_split (String.length s - 3) s ltac:(lia)) as Hsp.
  replace (String.length s - (String.length s - 3))%nat with 3%nat in Hsp by lia.
  rewrite Heq in Hsp. exact Hsp.
Qed.

Lemma filename_ok_has_dot : forall s, FilePath.filename_ok s = true -> contains_dot s = true.
Proof.
  intros s H. unfold FilePath.filename_ok in H. apply andb_true_iff in H. destruct H as [Hends _].
  rewrite (ends_go_recon s Hends), contains_dot_app.
  replace (contains_dot ".go") with true by reflexivity. apply Bool.orb_true_r.
Qed.

Lemma dir_component_neq_filename : forall d f,
  FilePath.dir_component_ok d = true -> FilePath.filename_ok f = true -> d <> f.
Proof.
  intros d f Hd Hf Heq. subst f.
  unfold FilePath.dir_component_ok in Hd. apply andb_true_iff in Hd. destruct Hd as [Hc _].
  pose proof (component_ok_no_dot d Hc) as Hnd. pose proof (filename_ok_has_dot d Hf) as Hyd.
  rewrite Hnd in Hyd. discriminate Hyd.
Qed.

(** a root source basename is never "go.mod", which ends in .mod rather than .go *)
Lemma filename_ok_neq_gomod : forall f, FilePath.filename_ok f = true -> f <> "go.mod".
Proof. intros f Hf Heq. subst f. vm_compute in Hf. discriminate Hf. Qed.

(** a nested file's first path component is a valid directory key, as the path grammar requires *)

Lemma first_component_hd : forall s, first_component s = List.hd EmptyString (FilePath.split_slash s).
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [first_component FilePath.split_slash].
  destruct (Ascii.eqb c "/"%char); [reflexivity|].
  rewrite IH. destruct (FilePath.split_slash s) as [|h t]; reflexivity.
Qed.

Lemma hd_app_l {A} (d : A) (l1 l2 : list A) : l1 <> [] -> List.hd d (l1 ++ l2) = List.hd d l1.
Proof. destruct l1; [contradiction | reflexivity]. Qed.

Lemma first_component_dir_ok : forall s,
  FilePath.path_ok s = true -> FilePath.parent_of s <> EmptyString ->
  FilePath.dir_component_ok (first_component s) = true.
Proof.
  intros s Hp Hpar. rewrite first_component_hd.
  unfold FilePath.path_ok in Hp.
  destruct (rev (FilePath.split_slash s)) as [|last rdirs] eqn:Erev; [discriminate Hp|].
  apply andb_true_iff in Hp. destruct Hp as [Hdirs _].
  assert (Hrd : rdirs <> []).
  { intro Hc. subst rdirs. apply Hpar. unfold FilePath.parent_of. rewrite Erev. reflexivity. }
  assert (Hss : FilePath.split_slash s = (rev rdirs ++ [last])%list).
  { rewrite <- (rev_involutive (FilePath.split_slash s)), Erev. reflexivity. }
  rewrite Hss.
  assert (Hrr : rev rdirs <> []).
  { intro Hc. apply (f_equal (@rev _)) in Hc. rewrite rev_involutive in Hc. exact (Hrd Hc). }
  rewrite (hd_app_l EmptyString (rev rdirs) [last] Hrr).
  rewrite forallb_forall in Hdirs. apply Hdirs. apply in_rev.
  destruct (rev rdirs) as [|h t] eqn:Er; [contradiction | left; reflexivity].
Qed.

(** every valid path contains a dot, because its last segment is a `.go` filename *)
Lemma contains_dot_split_slash : forall s, contains_dot s = existsb contains_dot (FilePath.split_slash s).
Proof.
  induction s as [|c s' IH]; [reflexivity|].
  cbn [FilePath.split_slash contains_dot].
  destruct (Ascii.eqb c "/"%char) eqn:E.
  - apply Ascii.eqb_eq in E. subst c. cbn [existsb contains_dot]. rewrite IH. reflexivity.
  - cbn [existsb].
    destruct (FilePath.split_slash s') as [|h t].
    + rewrite IH. cbn [existsb contains_dot]. rewrite !Bool.orb_false_r. reflexivity.
    + rewrite IH. cbn [existsb contains_dot]. rewrite Bool.orb_assoc. reflexivity.
Qed.

Lemma path_ok_has_dot : forall s, FilePath.path_ok s = true -> contains_dot s = true.
Proof.
  intros s Hp. rewrite contains_dot_split_slash. apply existsb_exists.
  unfold FilePath.path_ok in Hp.
  destruct (rev (FilePath.split_slash s)) as [|last rdirs] eqn:Erev; [discriminate Hp|].
  apply andb_true_iff in Hp. destruct Hp as [_ Hfn].
  exists last. split.
  - assert (Hin : In last (rev (FilePath.split_slash s))) by (rewrite Erev; left; reflexivity).
    rewrite <- in_rev in Hin. exact Hin.
  - apply filename_ok_has_dot. exact Hfn.
Qed.

(** the root layout as a standard string-keyed map, built by one fold and conflict-free by disjointness *)

Definition root_entry_of_file (b : FilePath.T * Syntax.File) : string * FreshRootEntryKind :=
  if String.eqb (FilePath.parent (fst b)) ""
  then (FilePath.text (fst b), SourceFileEntry (fst b))
  else (first_component (FilePath.text (fst b)), DirectoryEntry).

(** the root entry depends only on the path, so it factors through the key alone *)
Definition root_entry_of_path (fp : FilePath.T) : string * FreshRootEntryKind :=
  if String.eqb (FilePath.parent fp) ""
  then (FilePath.text fp, SourceFileEntry fp)
  else (first_component (FilePath.text fp), DirectoryEntry).

Lemma root_entry_of_file_eq_path : forall b, root_entry_of_file b = root_entry_of_path (fst b).
Proof. intro b. reflexivity. Qed.

Definition root_layout (p : Syntax.Program) : PackageMap.t FreshRootEntryKind :=
  fold_right (fun b acc => PackageMap.add (fst (root_entry_of_file b)) (snd (root_entry_of_file b)) acc)
             (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
             (Syntax.file_bindings (Syntax.files p)).

(** the layout over a bare key list, which the image bridge recomputes from the image's own keys *)
Definition root_layout_of_keys (ks : list FilePath.T) : PackageMap.t FreshRootEntryKind :=
  fold_right (fun fp acc => PackageMap.add (fst (root_entry_of_path fp)) (snd (root_entry_of_path fp)) acc)
             (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _)) ks.

Lemma root_layout_eq_of_keys : forall p,
  root_layout p = root_layout_of_keys (map fst (Syntax.file_bindings (Syntax.files p))).
Proof.
  intro p. unfold root_layout, root_layout_of_keys.
  induction (Syntax.file_bindings (Syntax.files p)) as [|b bs IH]; [reflexivity|].
  cbn [map fold_right]. rewrite IH, root_entry_of_file_eq_path. reflexivity.
Qed.

(* GENERIC fold-of-adds find: an absent key falls through to [init]; a present key gets its (unique) value. *)
Lemma fold_add_find_notin {A} (kv : (FilePath.T * Syntax.File) -> string * A) (init : PackageMap.t A)
    (l : list (FilePath.T * Syntax.File)) (e : string) :
  (forall b, In b l -> fst (kv b) <> e) ->
  PackageMap.find e (fold_right (fun b acc => PackageMap.add (fst (kv b)) (snd (kv b)) acc) init l) = PackageMap.find e init.
Proof.
  induction l as [|b l IH]; intro Hni; [reflexivity|].
  cbn [fold_right]. destruct (String.eqb (fst (kv b)) e) eqn:Eb.
  - apply String.eqb_eq in Eb. exfalso. exact (Hni b (or_introl eq_refl) Eb).
  - apply String.eqb_neq in Eb. rewrite PackageFacts.add_neq_o by exact Eb. apply IH. intros b' Hb'. apply Hni; right; exact Hb'.
Qed.

Lemma fold_add_find_in {A} (kv : (FilePath.T * Syntax.File) -> string * A) (init : PackageMap.t A)
    (l : list (FilePath.T * Syntax.File)) (e : string) (b0 : FilePath.T * Syntax.File) :
  In b0 l -> fst (kv b0) = e ->
  (forall b1 b2, In b1 l -> In b2 l -> fst (kv b1) = fst (kv b2) -> snd (kv b1) = snd (kv b2)) ->
  PackageMap.find e (fold_right (fun b acc => PackageMap.add (fst (kv b)) (snd (kv b)) acc) init l) = Some (snd (kv b0)).
Proof.
  induction l as [|b l IH]; intros Hin Hk Hval; [destruct Hin|].
  cbn [fold_right]. destruct (String.eqb (fst (kv b)) e) eqn:Eb.
  - apply String.eqb_eq in Eb. rewrite PackageFacts.add_eq_o by exact Eb. f_equal.
    apply (Hval b b0); [ left; reflexivity | exact Hin | rewrite Eb; symmetry; exact Hk ].
  - apply String.eqb_neq in Eb. rewrite PackageFacts.add_neq_o by exact Eb.
    destruct Hin as [Hb0|Hin]; [ subst b0; exfalso; exact (Eb Hk) |].
    apply IH; [ exact Hin | exact Hk | intros b1 b2 H1 H2; apply Hval; right; assumption ].
Qed.

(* the root-entry key uniquely determines its value: same key => same kind (the conflict audit, mapped). *)
Lemma root_entry_hval : forall b1 b2 : FilePath.T * Syntax.File,
  fst (root_entry_of_file b1) = fst (root_entry_of_file b2) ->
  snd (root_entry_of_file b1) = snd (root_entry_of_file b2).
Proof.
  intros b1 b2 Hk. unfold root_entry_of_file in *.
  destruct (String.eqb (FilePath.parent (fst b1)) "") eqn:E1;
    destruct (String.eqb (FilePath.parent (fst b2)) "") eqn:E2; cbn [fst snd] in *.
  - assert (Hp : fst b1 = fst b2) by (apply FilePath.equal; exact Hk). rewrite Hp. reflexivity.
  - exfalso. apply String.eqb_neq in E2.
    pose proof (path_ok_has_dot (FilePath.text (fst b1)) (FilePath.valid (fst b1))) as Hd1.
    pose proof (first_component_dir_ok (FilePath.text (fst b2)) (FilePath.valid (fst b2)) E2) as Hdc2.
    unfold FilePath.dir_component_ok in Hdc2. apply andb_true_iff in Hdc2. destruct Hdc2 as [Hc2 _].
    rewrite Hk, (component_ok_no_dot _ Hc2) in Hd1. discriminate Hd1.
  - exfalso. apply String.eqb_neq in E1.
    pose proof (path_ok_has_dot (FilePath.text (fst b2)) (FilePath.valid (fst b2))) as Hd2.
    pose proof (first_component_dir_ok (FilePath.text (fst b1)) (FilePath.valid (fst b1)) E1) as Hdc1.
    unfold FilePath.dir_component_ok in Hdc1. apply andb_true_iff in Hdc1. destruct Hdc1 as [Hc1 _].
    rewrite <- Hk, (component_ok_no_dot _ Hc1) in Hd2. discriminate Hd2.
  - reflexivity.
Qed.

(** a key is a directory entry exactly when some nested file has it as its first component *)
Lemma root_layout_dir_iff : forall p e,
  PackageMap.find e (root_layout p) = Some DirectoryEntry <->
  (exists b, In b (Syntax.file_bindings (Syntax.files p))
             /\ FilePath.parent (fst b) <> "" /\ first_component (FilePath.text (fst b)) = e).
Proof.
  intros p e. unfold root_layout. split.
  - intro Hfind.
    destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
                (Syntax.file_bindings (Syntax.files p))) eqn:Eex.
    + apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
      rewrite (fold_add_find_in root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
                 (Syntax.file_bindings (Syntax.files p)) e b Hin Hkey
                 (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hfind.
      injection Hfind as Hval. exists b.
      unfold root_entry_of_file in Hkey, Hval.
      destruct (String.eqb (FilePath.parent (fst b)) "") eqn:E; cbn [fst snd] in Hkey, Hval.
      * discriminate Hval.
      * apply String.eqb_neq in E. split; [ exact Hin | split; [ exact E | exact Hkey ] ].
    + assert (Hni : forall b, In b (Syntax.file_bindings (Syntax.files p)) -> fst (root_entry_of_file b) <> e).
      { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
        exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
      rewrite (fold_add_find_notin root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
                 (Syntax.file_bindings (Syntax.files p)) e Hni) in Hfind.
      destruct (String.eqb "go.mod" e) eqn:Eg.
      * apply String.eqb_eq in Eg. rewrite <- Eg, PackageFacts.add_eq_o in Hfind by reflexivity. discriminate Hfind.
      * apply String.eqb_neq in Eg. rewrite PackageFacts.add_neq_o in Hfind by exact Eg.
        rewrite PackageFacts.empty_o in Hfind. discriminate Hfind.
  - intros [b [Hin [Hpar Hfc]]].
    assert (Hkv : root_entry_of_file b = (e, DirectoryEntry)).
    { unfold root_entry_of_file. destruct (String.eqb (FilePath.parent (fst b)) "") eqn:E.
      - apply String.eqb_eq in E. exfalso. exact (Hpar E).
      - rewrite Hfc. reflexivity. }
    rewrite (fold_add_find_in root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
               (Syntax.file_bindings (Syntax.files p)) e b Hin (f_equal fst Hkv)
               (fun b1 b2 _ _ => root_entry_hval b1 b2)).
    rewrite Hkv. reflexivity.
Qed.

(** a root-entry key is never "go.mod", so the module entry cannot be overwritten *)
Lemma root_entry_key_neq_gomod : forall b, fst (root_entry_of_file b) <> "go.mod".
Proof.
  intro b. unfold root_entry_of_file.
  destruct (String.eqb (FilePath.parent (fst b)) "") eqn:E; cbn [fst]; intro Hc.
  - pose proof (FilePath.valid (fst b)) as Hok. rewrite Hc in Hok.
    vm_compute in Hok. discriminate Hok.
  - apply String.eqb_neq in E.
    pose proof (first_component_dir_ok (FilePath.text (fst b)) (FilePath.valid (fst b)) E) as Hdc.
    rewrite Hc in Hdc. vm_compute in Hdc. discriminate Hdc.
Qed.

(** the GENERIC fold-of-adds MEMBERSHIP: a key is in the fold iff it is an added key OR is in [init]. *)
Lemma fold_add_in_iff {A} (kv : (FilePath.T * Syntax.File) -> string * A) (init : PackageMap.t A)
    (l : list (FilePath.T * Syntax.File)) (e : string) :
  PackageMap.In e (fold_right (fun b acc => PackageMap.add (fst (kv b)) (snd (kv b)) acc) init l)
  <-> In e (map (fun b => fst (kv b)) l) \/ PackageMap.In e init.
Proof.
  induction l as [|b bs IH]; cbn [fold_right map].
  - split; [ intro H; right; exact H | intros [[]|H]; exact H ].
  - rewrite PackageFacts.add_in_iff, IH. split.
    + intros [He|[Hin|Hi]]; [ left; left; exact He | left; right; exact Hin | right; exact Hi ].
    + intros [[He|Hin]|Hi]; [ left; exact He | right; left; exact Hin | right; right; exact Hi ].
Qed.

(** "go.mod" always maps to the module entry, and it is the only key that does *)
Lemma root_layout_gomod : forall p, PackageMap.find "go.mod" (root_layout p) = Some GoModuleEntry.
Proof.
  intro p. unfold root_layout.
  rewrite (fold_add_find_notin root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
             (Syntax.file_bindings (Syntax.files p)) "go.mod" (fun b _ => root_entry_key_neq_gomod b)).
  apply PackageFacts.add_eq_o. reflexivity.
Qed.

Lemma root_layout_gomod_iff : forall p e,
  PackageMap.find e (root_layout p) = Some GoModuleEntry <-> e = "go.mod".
Proof.
  intros p e. split; [| intros ->; apply root_layout_gomod ].
  intro Hf. unfold root_layout in Hf.
  destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
              (Syntax.file_bindings (Syntax.files p))) eqn:Eex.
  - apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
    rewrite (fold_add_find_in root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
               (Syntax.file_bindings (Syntax.files p)) e b Hin Hkey
               (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hf.
    exfalso. injection Hf as Hval. unfold root_entry_of_file in Hval.
    destruct (String.eqb (FilePath.parent (fst b)) ""); cbn [snd] in Hval; discriminate Hval.
  - assert (Hni : forall b, In b (Syntax.file_bindings (Syntax.files p)) -> fst (root_entry_of_file b) <> e).
    { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
      exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
    rewrite (fold_add_find_notin root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
               (Syntax.file_bindings (Syntax.files p)) e Hni) in Hf.
    destruct (String.eqb "go.mod" e) eqn:Eg.
    + apply String.eqb_eq in Eg; symmetry; exact Eg.
    + apply String.eqb_neq in Eg. rewrite PackageFacts.add_neq_o, PackageFacts.empty_o in Hf by exact Eg. discriminate Hf.
Qed.

(** a key is a source-file entry exactly when some root-level file has that path *)
Lemma root_layout_source_iff : forall p e fp,
  PackageMap.find e (root_layout p) = Some (SourceFileEntry fp) <->
  (exists b, In b (Syntax.file_bindings (Syntax.files p))
             /\ FilePath.parent (fst b) = "" /\ FilePath.text (fst b) = e /\ fst b = fp).
Proof.
  intros p e fp. unfold root_layout. split.
  - intro Hf.
    destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
                (Syntax.file_bindings (Syntax.files p))) eqn:Eex.
    + apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
      rewrite (fold_add_find_in root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
                 (Syntax.file_bindings (Syntax.files p)) e b Hin Hkey
                 (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hf.
      injection Hf as Hval. exists b.
      unfold root_entry_of_file in Hkey, Hval.
      destruct (String.eqb (FilePath.parent (fst b)) "") eqn:E; cbn [fst snd] in Hkey, Hval.
      * apply String.eqb_eq in E. injection Hval as Hfp.
        split; [ exact Hin | split; [ exact E | split; [ exact Hkey | exact Hfp ] ] ].
      * discriminate Hval.
    + exfalso.
      assert (Hni : forall b, In b (Syntax.file_bindings (Syntax.files p)) -> fst (root_entry_of_file b) <> e).
      { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
        exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
      rewrite (fold_add_find_notin root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
                 (Syntax.file_bindings (Syntax.files p)) e Hni) in Hf.
      destruct (String.eqb "go.mod" e) eqn:Eg.
      * apply String.eqb_eq in Eg. rewrite <- Eg, PackageFacts.add_eq_o in Hf by reflexivity. discriminate Hf.
      * apply String.eqb_neq in Eg. rewrite PackageFacts.add_neq_o, PackageFacts.empty_o in Hf by exact Eg. discriminate Hf.
  - intros [b [Hin [Hpar [Hkey Hfp]]]].
    assert (Hkv : root_entry_of_file b = (e, SourceFileEntry fp)).
    { unfold root_entry_of_file. destruct (String.eqb (FilePath.parent (fst b)) "") eqn:E.
      - rewrite Hkey, Hfp. reflexivity.
      - apply String.eqb_neq in E. exfalso. exact (E Hpar). }
    rewrite (fold_add_find_in root_entry_of_file (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
               (Syntax.file_bindings (Syntax.files p)) e b Hin (f_equal fst Hkv)
               (fun b1 b2 _ _ => root_entry_hval b1 b2)).
    rewrite Hkv. reflexivity.
Qed.

(** the layout's keys are exactly "go.mod" plus each represented file's root-entry key *)
Lemma root_base_in_iff : forall e,
  PackageMap.In e (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty FreshRootEntryKind)) <-> e = "go.mod".
Proof.
  intro e. rewrite PackageFacts.add_in_iff, PackageFacts.empty_in_iff. split.
  - intros [He|[]]; symmetry; exact He.
  - intros ->. left; reflexivity.
Qed.

Lemma root_layout_domain : forall p e,
  PackageMap.In e (root_layout p) <->
  e = "go.mod" \/ In e (map (fun b => fst (root_entry_of_file b)) (Syntax.file_bindings (Syntax.files p))).
Proof.
  intros p e. unfold root_layout. rewrite fold_add_in_iff, root_base_in_iff.
  split; [ intros [Hin|He]; [ right; exact Hin | left; exact He ]
         | intros [He|Hin]; [ right; exact He | left; exact Hin ] ].
Qed.

(** the retained build plan and its preflight, which fails before compiling on an existing directory *)

Inductive FreshBuildDisposition : Type :=
| NoPackages
| DiscardMultiple (count : nat)
| WriteSingleMain (dir import_path output_name : string) (target : option FreshRootEntryKind).

(** the plan as a pure function of the spec, the package keys and the layout, so retention derives it *)
Definition fresh_build_plan_of (ms : ModuleSpec) (keys : list string)
    (rl : PackageMap.t FreshRootEntryKind) : FreshBuildDisposition :=
  match keys with
  | [] => NoPackages
  | dir :: nil =>
      let ip := package_import_path ms dir in
      let ex := default_exec_name ms dir in
      WriteSingleMain dir ip ex (PackageMap.find ex rl)
  | _ :: _ :: _ => DiscardMultiple (length keys)
  end.

(** one plan builder, so the retained buckets reproduce it once their keys are shown equal *)
Definition fresh_build_plan (p : Syntax.Program) : FreshBuildDisposition :=
  fresh_build_plan_of (Syntax.module_spec p) (selected_package_keys p) (root_layout p).

(* every selected package key is "" or the parent directory of a represented file. *)
Lemma selected_key_is_parent : forall p dir,
  In dir (selected_package_keys p) -> dir = ""%string \/ exists fp, FilePath.parent fp = dir.
Proof.
  intros p dir Hin. unfold selected_package_keys in Hin. apply in_map_iff in Hin.
  destruct Hin as [[k s] [Hfst Hinel]]. cbn in Hfst. subst k.
  assert (Hmt : PackageMap.MapsTo dir s (selected_packages p))
    by (apply PackageFacts.elements_mapsto_iff, InA_alt; exists (dir, s); split; [ split; reflexivity | exact Hinel ]).
  assert (Hex : exists b, In b (Syntax.file_bindings (Syntax.files p)) /\ FilePath.parent (fst b) = dir).
  { apply selected_iff_file. exists s. exact Hmt. }
  destruct Hex as [b [_ Hpar]]. right. exists (fst b). exact Hpar.
Qed.

(** a sole selected package's default executable name is never empty *)
Theorem fresh_build_plan_exec_nonempty : forall p dir ip ex t,
  fresh_build_plan p = WriteSingleMain dir ip ex t -> ex <> ""%string.
Proof.
  intros p dir ip ex t Hplan.
  unfold fresh_build_plan, fresh_build_plan_of in Hplan.
  destruct (selected_package_keys p) as [|d0 [|d1 r]] eqn:Ek; try discriminate Hplan.
  injection Hplan as _ _ Hex _.
  assert (Hdir : d0 = ""%string \/ exists fp, FilePath.parent fp = d0)
    by (apply (selected_key_is_parent p); rewrite Ek; left; reflexivity).
  rewrite <- Hex. apply (default_exec_name_nonempty (Syntax.module_spec p) d0 Hdir).
Qed.

(** the EXACT zero / single / multiple plan CLASSIFICATION by selected-package count. *)
Lemma fresh_build_plan_zero : forall p,
  selected_package_keys p = [] -> fresh_build_plan p = NoPackages.
Proof. intros p H. unfold fresh_build_plan, fresh_build_plan_of. rewrite H. reflexivity. Qed.

Lemma fresh_build_plan_multiple : forall p d1 d2 rest,
  selected_package_keys p = d1 :: d2 :: rest ->
  fresh_build_plan p = DiscardMultiple (selected_package_count p).
Proof. intros p d1 d2 rest H. unfold fresh_build_plan, fresh_build_plan_of, selected_package_count. rewrite H. reflexivity. Qed.

(** the plan's stored target is the layout's classification at the default output name *)
Lemma fresh_build_plan_single_target : forall p dir ip ex t,
  fresh_build_plan p = WriteSingleMain dir ip ex t -> t = PackageMap.find ex (root_layout p).
Proof.
  intros p dir ip ex t Hplan. unfold fresh_build_plan, fresh_build_plan_of in Hplan.
  destruct (selected_package_keys p) as [|d0 [|d1 r]] eqn:Ek; try discriminate Hplan.
  injection Hplan as _ _ Hex Ht. rewrite <- Hex. symmetry. exact Ht.
Qed.

(** the retained buckets' keys are the selected package keys, so the plan needs no second fold *)
Lemma bucket_keys_eq_selected : forall p (idx : Index.Snapshot.Syntax p),
  map fst (PackageMap.elements (program_package_refs idx)) = selected_package_keys p.
Proof.
  intros p idx. unfold selected_package_keys, selected_packages.
  apply Collections.package_same_domain_keys.
  intro dir. rewrite (program_package_refs_present idx dir). split.
  - intro Hmem. apply PackageFacts.in_find_iff. rewrite package_summaries_find, Hmem. discriminate.
  - intros [s Hmt]. apply PackageFacts.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
    destruct (list_dir_mem dir (Syntax.file_bindings (Syntax.files p))) eqn:E; [ reflexivity | discriminate Hmt ].
Qed.

(** the plan derived from the retained buckets and layout is the canonical one *)
Lemma fresh_build_plan_of_buckets : forall p (idx : Index.Snapshot.Syntax p),
  fresh_build_plan_of (Syntax.module_spec p) (map fst (PackageMap.elements (program_package_refs idx))) (root_layout p)
  = fresh_build_plan p.
Proof.
  intros p idx. rewrite (bucket_keys_eq_selected p idx). unfold fresh_build_plan. reflexivity.
Qed.

(* the preflight decision: reject ONLY a sole-main default output name that is an existing root directory. *)
Definition fresh_build_disposition_ok (d : FreshBuildDisposition) : bool :=
  match d with
  | WriteSingleMain _ _ _ (Some DirectoryEntry) => false
  | _ => true
  end.

Definition fresh_build_preflight_ok (p : Syntax.Program) : Prop :=
  fresh_build_disposition_ok (fresh_build_plan p) = true.

(* the ONLY command-level preflight failure: a sole selected package whose default exec name is a root DIR. *)
Lemma preflight_fails_iff : forall p,
  fresh_build_disposition_ok (fresh_build_plan p) = false <->
  (exists dir, selected_package_keys p = [dir]
     /\ PackageMap.find (default_exec_name (Syntax.module_spec p) dir) (root_layout p) = Some DirectoryEntry).
Proof.
  intros p. unfold fresh_build_plan, fresh_build_plan_of, fresh_build_disposition_ok.
  destruct (selected_package_keys p) as [|dir [|d2 rest]] eqn:Ek.
  - split; [ discriminate | intros [d [Hd _]]; discriminate Hd ].
  - cbn.
    destruct (PackageMap.find (default_exec_name (Syntax.module_spec p) dir) (root_layout p))
      as [k|] eqn:Ef.
    + destruct k; cbn.
      * split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
      * split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
      * split; [ intros _; exists dir; split; [reflexivity | exact Ef] | reflexivity ].
    + split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
  - cbn. split; [ discriminate | intros [d [Hd _]]; discriminate Hd ].
Qed.

(* the preflight fails when the default name equals a nested file's first component *)
Corollary preflight_fails_dir : forall p,
  ~ fresh_build_preflight_ok p <->
  (exists dir b, selected_package_keys p = [dir]
     /\ In b (Syntax.file_bindings (Syntax.files p)) /\ FilePath.parent (fst b) <> ""
     /\ first_component (FilePath.text (fst b)) = default_exec_name (Syntax.module_spec p) dir).
Proof.
  intros p. unfold fresh_build_preflight_ok. rewrite Bool.not_true_iff_false, preflight_fails_iff. split.
  - intros [dir [Hk Hf]]. apply (proj1 (root_layout_dir_iff p _)) in Hf.
    destruct Hf as [b [Hin [Hpar Hfc]]]. exists dir, b. repeat split; assumption.
  - intros [dir [b [Hk [Hin [Hpar Hfc]]]]]. exists dir. split; [ exact Hk |].
    apply (proj2 (root_layout_dir_iff p _)). exists b. repeat split; assumption.
Qed.

(** source validity, factored into the two independent Go rules the combined reading conflated *)
Definition SourceProgramValid (p : Syntax.Program) : Prop :=
  Typing.Program predeclared_type p /\ PackageRulesValid p.

(** the exactly-one property is a consequence of today's two rules, never the source authority *)
Lemma current_package_rules_exactly_one : forall p, PackageRulesValid p <-> current_grammar_one_main p.
Proof.
  intro p. unfold PackageRulesValid, PackageDeclsUnique, MainPackagesHaveEntry, current_grammar_one_main. split.
  - intros [Hle Hge] dir s Hmt. pose proof (Hle dir s Hmt); pose proof (Hge dir s Hmt); lia.
  - intros H. split; intros dir s Hmt; pose proof (H dir s Hmt); lia.
Qed.

(** the decidable source check reflects the live factored root directly *)
Lemma source_spec_valid_b_iff : forall p, source_spec_valid_b p = true <-> SourceProgramValid p.
Proof.
  intro p. unfold source_spec_valid_b, SourceProgramValid.
  rewrite Bool.andb_true_iff, program_typedb_iff, source_spec_package_rules_b_package_rules_valid. reflexivity.
Qed.

(** the specification decision reflects the same factored root, as the public source-validity surface *)
Lemma semantic_ok_b_source_program_valid (p : Syntax.Program) : semantic_ok_b p = true <-> SourceProgramValid p.
Proof. rewrite semantic_ok_b_source_spec_valid_b. apply source_spec_valid_b_iff. Qed.

(** the command-level diagnostic: one build-output reason when the preflight fails, and none otherwise *)

Definition sole_package_ref (p : Syntax.Program) (dir : string) : option (PackageRef p) :=
  match Bool.bool_dec (package_present_b p dir) true with
  | left H  => Some (MakePackageRef p dir H)
  | right _ => None
  end.

Lemma sole_package_ref_some : forall p dir,
  package_present_b p dir = true -> exists pk, sole_package_ref p dir = Some pk.
Proof.
  intros p dir H. unfold sole_package_ref.
  destruct (Bool.bool_dec (package_present_b p dir) true) as [Ht|Hf]; [ eexists; reflexivity | destruct (Hf H) ].
Qed.

(* a sole selected package is present (it is a key of the package-summary map, so a file has that parent). *)
Lemma sole_package_present : forall p dir,
  selected_package_keys p = [dir] -> package_present_b p dir = true.
Proof.
  intros p dir Hk.
  assert (Hin : In dir (selected_package_keys p)) by (rewrite Hk; left; reflexivity).
  unfold selected_package_keys in Hin. apply in_map_iff in Hin.
  destruct Hin as [[k s] [Hfst Hinel]]. cbn in Hfst. subst k.
  assert (Hmt : PackageMap.MapsTo dir s (selected_packages p))
    by (apply PackageFacts.elements_mapsto_iff, InA_alt; exists (dir, s); split; [split; reflexivity | exact Hinel]).
  unfold package_present_b. unfold selected_packages in Hmt.
  apply PackageFacts.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (Syntax.file_bindings (Syntax.files p))); [ reflexivity | discriminate Hmt ].
Qed.

(* stated over a given plan, so elaboration threads its one retained plan through the failure branch *)
Definition fresh_build_diagnostics_of (p : Syntax.Program) (plan : FreshBuildDisposition) : list (DiagnosticReason p) :=
  match plan with
  | WriteSingleMain dir _ output_name (Some DirectoryEntry) =>
      match sole_package_ref p dir with
      | Some pk => [BuildOutputIsDirectory pk output_name]
      | None    => []
      end
  | _ => []
  end.

Definition fresh_build_diagnostics (p : Syntax.Program) : list (DiagnosticReason p) :=
  fresh_build_diagnostics_of p (fresh_build_plan p).

(** the one report builder: a failed preflight takes precedence over the semantic diagnostics *)
Definition command_diagnostics_of (p : Syntax.Program) (plan : FreshBuildDisposition)
    (semantic_ds : list (DiagnosticReason p)) : list (DiagnosticReason p) :=
  if fresh_build_disposition_ok plan then semantic_ds else fresh_build_diagnostics_of p plan.

Lemma fresh_build_diagnostics_nil_iff : forall p,
  fresh_build_diagnostics p = [] <-> fresh_build_preflight_ok p.
Proof.
  intros p. unfold fresh_build_diagnostics, fresh_build_diagnostics_of, fresh_build_preflight_ok, fresh_build_disposition_ok, fresh_build_plan.
  destruct (selected_package_keys p) as [|dir [|d2 rest]] eqn:Ek; cbn.
  - split; reflexivity.
  - destruct (PackageMap.find (default_exec_name (Syntax.module_spec p) dir) (root_layout p)) as [k|] eqn:Ef.
    + destruct k; cbn.
      * split; reflexivity.
      * split; reflexivity.
      * destruct (sole_package_ref p dir) as [pk|] eqn:Es.
        -- split; [ discriminate | discriminate ].
        -- exfalso. destruct (sole_package_ref_some p dir (sole_package_present p dir Ek)) as [pk Hpk].
           rewrite Hpk in Es. discriminate Es.
    + split; reflexivity.
  - split; reflexivity.
Qed.

(** full program-input equality is both the module spec and the file map *)
Definition ProgramInputEqual (p1 p2 : Syntax.Program) : Prop :=
  Syntax.module_spec p1 = Syntax.module_spec p2 /\ Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2).

(* the selected-package enumeration and the root layout depend only on the file map. *)
Lemma selected_package_keys_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> selected_package_keys p1 = selected_package_keys p2.
Proof.
  intros p1 p2 Heq. unfold selected_package_keys, selected_packages.
  rewrite (Collections.package_elements_equal _ _ (package_summaries_equal _ _ Heq)). reflexivity.
Qed.

Lemma root_layout_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> root_layout p1 = root_layout p2.
Proof.
  intros p1 p2 Heq. unfold root_layout, Syntax.file_bindings.
  rewrite (Collections.file_elements_equal _ _ Heq). reflexivity.
Qed.

Lemma fresh_build_plan_input_equal : forall p1 p2,
  ProgramInputEqual p1 p2 -> fresh_build_plan p1 = fresh_build_plan p2.
Proof.
  intros p1 p2 [Hm Hf]. unfold fresh_build_plan.
  rewrite (selected_package_keys_equal _ _ Hf), Hm, (root_layout_equal _ _ Hf). reflexivity.
Qed.

Lemma fresh_build_disposition_input_equal : forall p1 p2,
  ProgramInputEqual p1 p2 ->
  fresh_build_disposition_ok (fresh_build_plan p1) = fresh_build_disposition_ok (fresh_build_plan p2).
Proof. intros p1 p2 H. rewrite (fresh_build_plan_input_equal _ _ H). reflexivity. Qed.

(** a failed preflight makes the report exactly the build-output reason, hiding the semantic ones *)
Definition elaboration_diagnostics (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) : list (DiagnosticReason p) :=
  command_diagnostics_of p (fresh_build_plan p) (semantic_diagnostics p idx).

(** the retained source validity is the factored one, of which the exactly-one reading is a consequence *)
Lemma elaboration_no_diags_source_valid : forall p idx, elaboration_diagnostics p idx = nil -> SourceProgramValid p.
Proof.
  intros p idx He.
  unfold elaboration_diagnostics, command_diagnostics_of in He. destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
  - exact (proj1 (semantic_ok_b_source_program_valid p) (proj1 (semantic_diagnostics_empty_iff p idx) He)).
  - apply (proj1 (fresh_build_diagnostics_nil_iff p)) in He. unfold fresh_build_preflight_ok in He.
    rewrite He in Ep. discriminate Ep.
Qed.

Lemma elaboration_no_diags_preflight : forall p idx, elaboration_diagnostics p idx = nil -> fresh_build_preflight_ok p.
Proof.
  intros p idx He. unfold elaboration_diagnostics, command_diagnostics_of in He. destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
  - unfold fresh_build_preflight_ok. exact Ep.
  - exact (proj1 (fresh_build_diagnostics_nil_iff p) He).
Qed.

Lemma elaboration_diagnostics_eq_semantic : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = true -> elaboration_diagnostics p idx = semantic_diagnostics p idx.
Proof. intros p idx H. unfold elaboration_diagnostics, command_diagnostics_of. rewrite H. reflexivity. Qed.

Lemma elaboration_diagnostics_eq_fresh : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = false -> elaboration_diagnostics p idx = fresh_build_diagnostics p.
Proof. intros p idx H. unfold elaboration_diagnostics, command_diagnostics_of. rewrite H. reflexivity. Qed.

(* end of the block — restore the default scope so the elaboration machinery's list [++] is list append. *)
Close Scope string_scope.

(** admissibility is the build-output preflight passing together with the source being valid *)
Definition Admissible (p : Syntax.Program) : Prop := fresh_build_preflight_ok p /\ SourceProgramValid p.

(** the command-ordered report is empty exactly on admissible programs *)
Lemma elaboration_diagnostics_nil_iff_admissible : forall p idx, elaboration_diagnostics p idx = nil <-> Admissible p.
Proof.
  intros p idx. unfold Admissible. split.
  - intro He. split; [ exact (elaboration_no_diags_preflight p idx He)
                     | exact (elaboration_no_diags_source_valid p idx He) ].
  - intros [Hpf Hsv]. unfold elaboration_diagnostics, command_diagnostics_of. unfold fresh_build_preflight_ok in Hpf. rewrite Hpf.
    apply (proj2 (semantic_diagnostics_empty_iff p idx)), (proj2 (semantic_ok_b_source_program_valid p)). exact Hsv.
Qed.

(** the report over the retained bucket-derived plan is the canonical one *)
Lemma command_plan_diags_eq (p : Syntax.Program) (ip : Index.Program p) :
  command_diagnostics_of p
    (fresh_build_plan_of (Syntax.module_spec p)
       (map fst (PackageMap.elements (program_package_refs (Index.indexed_syntax ip)))) (root_layout p))
    (semantic_diagnostics p (Index.indexed_syntax ip))
  = elaboration_diagnostics p (Index.indexed_syntax ip).
Proof.
  rewrite (fresh_build_plan_of_buckets p (Index.indexed_syntax ip)).
  unfold elaboration_diagnostics. reflexivity.
Qed.


(** the alias pairs are distinct source syntax with the same resolved semantic type *)
Example predeclared_byte_is_uint8 : predeclared_type (Syntax.type_expr_of_name Names.Byte) = Typing.IntegerType Integer.Uint8. Proof. reflexivity. Qed.
Example predeclared_rune_is_int32 : predeclared_type (Syntax.type_expr_of_name Names.Rune) = Typing.IntegerType Integer.Int32. Proof. reflexivity. Qed.
Theorem tnfact_byte_uint8_same_type :
  MakeTypeNameFact (predeclared_type (Syntax.type_expr_of_name Names.Byte))
  = MakeTypeNameFact (predeclared_type (Syntax.type_expr_of_name Names.Uint8)).
Proof. reflexivity. Qed.
Theorem tnfact_rune_int32_same_type :
  MakeTypeNameFact (predeclared_type (Syntax.type_expr_of_name Names.Rune))
  = MakeTypeNameFact (predeclared_type (Syntax.type_expr_of_name Names.Int32)).
Proof. reflexivity. Qed.
Theorem tsyn_byte_neq_uint8 : Syntax.type_expr_of_name Names.Byte <> Syntax.type_expr_of_name Names.Uint8.
Proof.
  intro H. apply (f_equal Syntax.type_expr_name) in H. rewrite !Syntax.type_expr_name_of in H. discriminate H.
Qed.
Theorem tsyn_rune_neq_int32 : Syntax.type_expr_of_name Names.Rune <> Syntax.type_expr_of_name Names.Int32.
Proof.
  intro H. apply (f_equal Syntax.type_expr_name) in H. rewrite !Syntax.type_expr_name_of in H. discriminate H.
Qed.

(** the one closed conjunction pinning every predeclared mapping, aliases included *)
Theorem predeclared_all_sixteen :
     predeclared_type (Syntax.type_expr_of_name Names.Int)        = Typing.IntegerType Integer.Int
  /\ predeclared_type (Syntax.type_expr_of_name Names.Int8)       = Typing.IntegerType Integer.Int8
  /\ predeclared_type (Syntax.type_expr_of_name Names.Int16)      = Typing.IntegerType Integer.Int16
  /\ predeclared_type (Syntax.type_expr_of_name Names.Int32)      = Typing.IntegerType Integer.Int32
  /\ predeclared_type (Syntax.type_expr_of_name Names.Int64)      = Typing.IntegerType Integer.Int64
  /\ predeclared_type (Syntax.type_expr_of_name Names.Uint)       = Typing.IntegerType Integer.Uint
  /\ predeclared_type (Syntax.type_expr_of_name Names.Uint8)      = Typing.IntegerType Integer.Uint8
  /\ predeclared_type (Syntax.type_expr_of_name Names.Uint16)     = Typing.IntegerType Integer.Uint16
  /\ predeclared_type (Syntax.type_expr_of_name Names.Uint32)     = Typing.IntegerType Integer.Uint32
  /\ predeclared_type (Syntax.type_expr_of_name Names.Uint64)     = Typing.IntegerType Integer.Uint64
  /\ predeclared_type (Syntax.type_expr_of_name Names.Float32)    = Typing.FloatType F32
  /\ predeclared_type (Syntax.type_expr_of_name Names.Float64)    = Typing.FloatType F64
  /\ predeclared_type (Syntax.type_expr_of_name Names.Complex64)  = Typing.ComplexType C64
  /\ predeclared_type (Syntax.type_expr_of_name Names.Complex128) = Typing.ComplexType C128
  /\ predeclared_type (Syntax.type_expr_of_name Names.Byte)       = Typing.IntegerType Integer.Uint8
  /\ predeclared_type (Syntax.type_expr_of_name Names.Rune)       = Typing.IntegerType Integer.Int32.
Proof. repeat split; reflexivity. Qed.


(** the alias scars: each alias accepts and rejects exactly where its resolved type does *)
Example single_rounding_byte_0_accepted   : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.IntegerLiteral 0))   = Some (Typing.IntegerType Integer.Uint8). Proof. reflexivity. Qed.
Example single_rounding_byte_255_accepted : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.IntegerLiteral 255)) = Some (Typing.IntegerType Integer.Uint8). Proof. reflexivity. Qed.
Example single_rounding_byte_256_rejected : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.IntegerLiteral 256)) = None. Proof. reflexivity. Qed.
Example single_rounding_byte_m1_rejected  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.NegatedIntegerLiteral 1))   = None. Proof. reflexivity. Qed.
Example single_rounding_uint8_255_eq_byte : constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 255))
                               = constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Byte)  (Syntax.IntegerLiteral 255)). Proof. reflexivity. Qed.
Example single_rounding_rune_min_accepted  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Rune) (Syntax.NegatedIntegerLiteral 2147483648)) = Some (Typing.IntegerType Integer.Int32). Proof. reflexivity. Qed.
Example single_rounding_rune_max_accepted  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Rune) (Syntax.IntegerLiteral 2147483647))  = Some (Typing.IntegerType Integer.Int32). Proof. reflexivity. Qed.
Example single_rounding_rune_under_rejected : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Rune) (Syntax.NegatedIntegerLiteral 2147483649)) = None. Proof. reflexivity. Qed.
Example single_rounding_rune_over_rejected  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Rune) (Syntax.IntegerLiteral 2147483648))  = None. Proof. reflexivity. Qed.
Example single_rounding_int32_65_eq_rune : constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 65))
                              = constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Rune)  (Syntax.IntegerLiteral 65)). Proof. reflexivity. Qed.
(** the matching semantic targets, whose accept and reject endpoints coincide with the aliases' *)
Example single_rounding_uint8_0_accepted    : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 0))          = Some (Typing.IntegerType Integer.Uint8). Proof. reflexivity. Qed.
Example single_rounding_uint8_255_accepted  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 255))        = Some (Typing.IntegerType Integer.Uint8). Proof. reflexivity. Qed.
Example single_rounding_uint8_256_rejected  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 256))        = None. Proof. reflexivity. Qed.
Example single_rounding_uint8_m1_rejected   : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.NegatedIntegerLiteral 1))          = None. Proof. reflexivity. Qed.
Example single_rounding_int32_min_accepted  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.NegatedIntegerLiteral 2147483648)) = Some (Typing.IntegerType Integer.Int32). Proof. reflexivity. Qed.
Example single_rounding_int32_max_accepted  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 2147483647)) = Some (Typing.IntegerType Integer.Int32). Proof. reflexivity. Qed.
Example single_rounding_int32_under_rejected : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.NegatedIntegerLiteral 2147483649)) = None. Proof. reflexivity. Qed.
Example single_rounding_int32_over_rejected  : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 2147483648)) = None. Proof. reflexivity. Qed.
(** repeated equal type names at distinct occurrences give distinct references and equal facts *)
Example single_rounding_nested_byte_uint16 : resolve Typing.PrintlnArgument
  (Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.Convert (Syntax.type_expr_of_name Names.Uint16) (Syntax.IntegerLiteral 255))) = Some (Typing.IntegerType Integer.Uint8). Proof. reflexivity. Qed.

(** a conversion target's carried proof forces one of the sixteen closed names, so nothing else is a target *)
Example excl_bool       : Names.classify "bool" = None.        Proof. reflexivity. Qed.
Example excl_string     : Names.classify "string" = None.      Proof. reflexivity. Qed.
Example excl_uintptr    : Names.classify "uintptr" = None.     Proof. reflexivity. Qed.
Example excl_any        : Names.classify "any" = None.         Proof. reflexivity. Qed.
Example excl_error      : Names.classify "error" = None.       Proof. reflexivity. Qed.
Example excl_comparable : Names.classify "comparable" = None.  Proof. reflexivity. Qed.
Example excl_foo        : Names.classify "foo" = None.         Proof. reflexivity. Qed.
Example excl_qualified  : Names.classify "pkg.T" = None.       Proof. reflexivity. Qed.
Fail Definition excl_bool_target : Syntax.TypeExpr :=
  Syntax.NamedType (Syntax.Unqualified (Names.MakeSupportedType (Names.MakeIdentifier "bool" eq_refl) Names.Int eq_refl)).

(** the representative conversion fixtures: one accept and one reject per family, plus the scars *)
Example representable_int8_127_accept : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 127)) = Some (Typing.IntegerType Integer.Int8). Proof. reflexivity. Qed.
Example representable_int8_128_reject : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128)) = None. Proof. reflexivity. Qed.
Example representable_f32_accept      : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_15em1)) = Some (Typing.FloatType F32). Proof. reflexivity. Qed.
Example representable_f32_bool_reject : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.BoolLiteral true)) = None. Proof. reflexivity. Qed.
Example representable_c64_accept      : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5)) = Some (Typing.ComplexType C64). Proof. vm_compute. reflexivity. Qed.
Example representable_c128_str_reject : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.StringLiteral "x")) = None. Proof. reflexivity. Qed.
Example representable_nested_accept   : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127))) = Some (Typing.IntegerType Integer.Int8). Proof. reflexivity. Qed.
Example representable_nested_reject   : resolve Typing.PrintlnArgument (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 128))) = None. Proof. reflexivity. Qed.
Example representable_same_f32_identity :
  constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_single_rounding)))
  = constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_single_rounding)). Proof. vm_compute. reflexivity. Qed.
Example representable_scalar_double_round_single_rounding :
  constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_single_rounding))
  <> constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral Typing.decimal_single_rounding))). Proof. vm_compute. discriminate. Qed.
Example representable_complex_component_single_rounding :
  constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0)))
  <> constant_info (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64)
        (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0)))). Proof. vm_compute. discriminate. Qed.
(** a wrong-kind occurrence has no type-name fact, so the table's domain is exactly the type names *)
Example representable_no_tnfact_on_expr : forall e par role sub,
  occurrence_type_name_fact (Index.MakeOccurrence Index.ExpressionKind (Index.ExpressionView e) (Some par) role sub) = None.
Proof. reflexivity. Qed.


(** the whole-elaboration object, retained rather than discarded, with its head dependently linked *)
Definition package_bucket_diagnostics_from_refs {p} (refs : PackageMap.t (list (Index.DeclRef p)))
    (Hpres : forall dir l, PackageMap.MapsTo dir l refs -> package_present_b p dir = true)
    : list (DiagnosticReason p) :=
  bucket_diags_elems refs Hpres (PackageMap.elements refs) (elements_all_mapsto refs).

(* the presence fact in the shape the fold wants, derived from a map's own domain characterisation. *)
Definition bucket_present_of_domain {p} (refs : PackageMap.t (list (Index.DeclRef p)))
    (Hdom : forall dir, PackageMap.In dir refs
                        <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true)
    : forall dir l, PackageMap.MapsTo dir l refs -> package_present_b p dir = true :=
  fun dir l Hmt => proj1 (Hdom dir) (ex_intro _ l Hmt).

(** the core is abstract outside this module, so a client cannot assemble a peer, well-formed or not *)
Module Type ELABORATION.
  Parameter Core : Syntax.Program -> Type.

  Parameter core_input : forall {p}, Core p -> Input p.
  Parameter phase : forall {p} (core : Core p), Phase (core_input core).

  Parameter core_package_refs : forall {p}, Core p -> PackageMap.t (list (Index.DeclRef p)).
  Parameter core_package_refs_from_visit : forall {p} (core : Core p),
    core_package_refs core
    = program_package_refs_from_visit (index (core_input core)) (input_visit (core_input core)).
  Parameter core_package_present : forall {p} (core : Core p) dir,
    PackageMap.In dir (core_package_refs core)
    <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true.
  Parameter core_package_len : forall {p} (core : Core p) dir l,
    PackageMap.find dir (core_package_refs core) = Some l ->
    length l = package_main_count dir (Syntax.files p).
  Parameter core_package_belongs : forall {p} (core : Core p) dir l,
    PackageMap.find dir (core_package_refs core) = Some l ->
    forall d, In d l ->
    FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref d))) = dir.

  Parameter core_layout : forall {p}, Core p -> PackageMap.t FreshRootEntryKind.
  Parameter core_layout_exact : forall {p} (core : Core p), core_layout core = root_layout p.

  Parameter core_plan : forall {p}, Core p -> FreshBuildDisposition.
  Parameter core_plan_exact : forall {p} (core : Core p),
    core_plan core = fresh_build_plan_of (Syntax.module_spec p)
                       (map fst (PackageMap.elements (core_package_refs core))) (core_layout core).

  Parameter core_raw_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
  Parameter core_raw_diagnostics_exact : forall {p} (core : Core p),
    core_raw_diagnostics core
    = phase_diags (phase core)
      ++ package_bucket_diagnostics_from_refs (core_package_refs core)
           (bucket_present_of_domain (core_package_refs core) (core_package_present core)).

  Parameter core_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
  Parameter core_diagnostics_exact : forall {p} (core : Core p),
    core_diagnostics core
    = command_diagnostics_of p (core_plan core)
        (bucket_flatten (node_keyed (core_raw_diagnostics core))
         ++ package_primary (core_raw_diagnostics core)).

  (* the decision is transparent so a caller can destruct it, but indexed so it cannot be moved *)
  Inductive Decision {p} (core : Core p) : Type :=
  | AcceptedDecision (Hnil : core_diagnostics core = nil)
  | RejectedDecision (Hne : core_diagnostics core <> nil).

  Parameter Elaboration : Syntax.Program -> Type.
  Parameter elaboration_core : forall {p}, Elaboration p -> Core p.
  Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).
  Parameter elaborate : forall p : Syntax.Program, Elaboration p.
End ELABORATION.

Module Elaborations : ELABORATION.
  Record CoreRepresentation (p : Syntax.Program) : Type := MakeCore {
    core_input : Input p ;
    phase : Phase core_input ;

    (* the buckets are built once from this core's own visit and stored with the evidence tying them to it *)
    core_package_refs : PackageMap.t (list (Index.DeclRef p)) ;
    core_package_refs_from_visit :
      core_package_refs = program_package_refs_from_visit (index core_input) (input_visit core_input) ;
    core_package_present : forall dir,
      PackageMap.In dir core_package_refs <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true ;
    core_package_len : forall dir l,
      PackageMap.find dir core_package_refs = Some l -> length l = package_main_count dir (Syntax.files p) ;
    core_package_belongs : forall dir l, PackageMap.find dir core_package_refs = Some l ->
      forall d, In d l ->
      FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref d))) = dir ;

    core_layout : PackageMap.t FreshRootEntryKind ;
    core_layout_exact : core_layout = root_layout p ;

    core_plan : FreshBuildDisposition ;
    core_plan_exact :
      core_plan = fresh_build_plan_of (Syntax.module_spec p)
                    (map fst (PackageMap.elements core_package_refs)) core_layout ;

    core_raw_diagnostics : list (DiagnosticReason p) ;
    (* the raw list is this core's own phase and package diagnostics, so nothing consults a rebuild *)
    core_raw_diagnostics_exact :
      core_raw_diagnostics
      = phase_diags phase
        ++ package_bucket_diagnostics_from_refs core_package_refs
             (bucket_present_of_domain core_package_refs core_package_present) ;

    core_diagnostics : list (DiagnosticReason p) ;
    core_diagnostics_exact :
      core_diagnostics = command_diagnostics_of p core_plan
        (bucket_flatten (node_keyed core_raw_diagnostics) ++ package_primary core_raw_diagnostics)
  }.
  Arguments MakeCore {p} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  Arguments core_input {p} _.  Arguments phase {p} _.
  Arguments core_package_refs {p} _.  Arguments core_package_refs_from_visit {p} _.
  Arguments core_package_present {p} _.  Arguments core_package_len {p} _.
  Arguments core_package_belongs {p} _.
  Arguments core_layout {p} _.  Arguments core_layout_exact {p} _.
  Arguments core_plan {p} _.  Arguments core_plan_exact {p} _.
  Arguments core_raw_diagnostics {p} _.  Arguments core_raw_diagnostics_exact {p} _.
  Arguments core_diagnostics {p} _.  Arguments core_diagnostics_exact {p} _.
  Definition Core (p : Syntax.Program) : Type := CoreRepresentation p.

  Inductive Decision {p} (core : Core p) : Type :=
  | AcceptedDecision (Hnil : core_diagnostics core = nil)
  | RejectedDecision (Hne : core_diagnostics core <> nil).
  Arguments AcceptedDecision {p core} _.
  Arguments RejectedDecision {p core} _.



  Record ElaborationRepresentation (p : Syntax.Program) : Type := MakeElaboration {
    elaboration_core     : Core p;
    decision : Decision elaboration_core
  }.
  Arguments MakeElaboration {p} _ _.
  Arguments elaboration_core {p} _.
  Arguments decision {p} _.
  Definition Elaboration (p : Syntax.Program) : Type := ElaborationRepresentation p.

  Definition list_is_nil {A} (l : list A) : {l = nil} + {l <> nil}.
  Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

  Definition decision_of_core {p} (core : Core p) : Decision core :=
    match list_is_nil (core_diagnostics core) with
    | left He   => AcceptedDecision He
    | right Hne => RejectedDecision Hne
    end.

  Definition build_elaboration_core (p : Syntax.Program) (ip : Index.Program p) : Core p :=
    let input := build_compilation_input p ip in
    let ph    := build_expression_phase input in
    let refs  := program_package_refs_from_visit (index input) (input_visit input) in
    let pres  := package_refs_present_at (index input) (input_visit input) (input_visit_ok input) in
    let lay   := root_layout p in
    let pl    := fresh_build_plan_of (Syntax.module_spec p) (map fst (PackageMap.elements refs)) lay in
    let raw   := phase_diags ph
                 ++ package_bucket_diagnostics_from_refs refs (bucket_present_of_domain refs pres) in
    MakeCore input ph
      refs eq_refl
      pres
      (package_refs_bucket_len_at (index input) (input_visit input) (input_visit_ok input))
      (package_refs_belongs_at (index input) (input_visit input) (input_visit_ok input))
      lay eq_refl
      pl eq_refl
      raw eq_refl
      (command_diagnostics_of p pl (bucket_flatten (node_keyed raw) ++ package_primary raw)) eq_refl.

  Definition elaborate_at {p : Syntax.Program} (ip : Index.Program p) : Elaboration p :=
    let core := build_elaboration_core p ip in
    MakeElaboration core (decision_of_core core).

  Definition elaborate (p : Syntax.Program) : Elaboration p :=
    elaborate_at (Index.index_program p).
End Elaborations.
Include Elaborations.
Arguments AcceptedDecision {p core} _.
Arguments RejectedDecision {p core} _.

(* the capability is not indexed by its source, so one bridging lemma carries a claim to it *)
Lemma core_prop_at_source (P : forall q, Core q -> Prop) {p q} (c : Core p) (H : p = q) :
  P q (eq_rect p Core c q H) -> P p c.
Proof. destruct H. exact (fun x => x). Qed.

(* the retained index and syntax index, projected — never reconstructed by [Index.index_program]. *)
Definition core_indexed {p} (core : Core p) : Index.Program p := indexed (core_input core).
Definition core_index {p} (core : Core p) : Index.Snapshot.Syntax p := index (core_input core).

(* the stored buckets ARE the canonical fold of the retained index (via the input's own visit evidence). *)
Lemma core_package_refs_canonical {p} (core : Core p) :
  core_package_refs core = program_package_refs (core_index core).
Proof.
  rewrite (core_package_refs_from_visit core).
  unfold program_package_refs, core_index. rewrite (input_visit_ok (core_input core)). reflexivity.
Qed.

(* the one core construction: input, phase, buckets, layout, plan and diagnostics, each exactly once *)
Lemma core_package_diags_canonical {p} (core : Core p) :
  package_bucket_diagnostics_from_refs (core_package_refs core)
    (bucket_present_of_domain (core_package_refs core) (core_package_present core))
  = package_diags (core_index core).
Proof.
  unfold package_bucket_diagnostics_from_refs, package_diags.
  generalize (bucket_present_of_domain (core_package_refs core) (core_package_present core)).
  generalize (elements_all_mapsto (core_package_refs core)).
  rewrite (core_package_refs_canonical core).
  intros Ha Hp. apply bucket_diags_elems_proof_irrelevant.
Qed.

(* the core's raw fold is the canonical diagnostic list, for any core rather than a fresh one *)
Lemma core_raw_semantic {p} (core : Core p) :
  bucket_flatten (node_keyed (core_raw_diagnostics core)) ++ package_primary (core_raw_diagnostics core)
  = semantic_diagnostics p (core_index core).
Proof.
  rewrite (core_raw_diagnostics_exact core), (core_package_diags_canonical core). unfold core_index.
  rewrite (phase_diags_eq_expr_diags (core_input core) (phase core)). reflexivity.
Qed.

(** the retained package provenance as theorems, all by reflexivity and none by equality to a rerun *)
Theorem core_refs_fold_own_visit : forall p (core : Core p),
  core_package_refs core
  = program_package_refs_from_visit (index (core_input core)) (input_visit (core_input core)).
Proof. intros p core. exact (core_package_refs_from_visit core). Qed.

Theorem core_raw_diagnostics_consume_retained_refs : forall p (core : Core p),
  core_raw_diagnostics core
  = phase_diags (phase core)
    ++ package_bucket_diagnostics_from_refs (core_package_refs core)
         (bucket_present_of_domain (core_package_refs core) (core_package_present core)).
Proof. intros p core. exact (core_raw_diagnostics_exact core). Qed.

(** the command-ordered list at one node-anchored diagnostic is that same singleton *)
Lemma core_diagnostics_of_node_singleton {p} (core : Core p) (d : DiagnosticReason p) k :
  core_raw_diagnostics core = [d] ->
  diag_node_key d = Some k ->
  fresh_build_disposition_ok (core_plan core) = true ->
  core_diagnostics core = [d].
Proof.
  intros Hraw Hk Hok.
  rewrite (core_diagnostics_exact core), Hraw.
  unfold command_diagnostics_of. rewrite Hok.
  unfold node_keyed, package_primary, bucket_flatten. cbn [flat_map]. rewrite Hk.
  cbn [app fold_right]. unfold bucket_add. cbn [fst snd].
  cbn. reflexivity.
Qed.

(* a specification bridge: the core's own decision is the canonical one, for any core *)
Lemma core_diagnostics_eq_elaboration {p} (core : Core p) :
  core_diagnostics core = elaboration_diagnostics p (core_index core).
Proof.
  rewrite (core_diagnostics_exact core), (core_plan_exact core), (core_layout_exact core),
          (core_package_refs_canonical core), (core_raw_semantic core).
  exact (command_plan_diags_eq p (core_indexed core)).
Qed.

(* the stored plan is the source-level one, as a bridge rather than a route to recover it *)
Lemma core_plan_is_fresh_build_plan {p} (core : Core p) : core_plan core = fresh_build_plan p.
Proof.
  rewrite (core_plan_exact core), (core_layout_exact core), (core_package_refs_canonical core).
  exact (fresh_build_plan_of_buckets p (core_index core)).
Qed.

(** the accepted view is indexed by its core and that core's acceptance, so the two cannot be separated *)
Module Type ACCEPTED_FACTS.
  Parameter Facts : forall {p : Syntax.Program} (core : Core p),
    core_diagnostics core = nil -> Type.
  Parameter source_valid : forall {p} {core : Core p} {accepted}, Facts core accepted -> SourceProgramValid p.
  Parameter preflight : forall {p} {core : Core p} {accepted}, Facts core accepted -> fresh_build_preflight_ok p.
  Parameter core_facts : forall {p} (core : Core p) (Hnil : core_diagnostics core = nil), Facts core Hnil.
End ACCEPTED_FACTS.

Module AcceptedFacts : ACCEPTED_FACTS.
  Record FactsRepresentation {p : Syntax.Program} (core : Core p)
      (accepted : core_diagnostics core = nil) : Type := MakeFacts {
    source_valid : SourceProgramValid p ;
    (* the retained preflight evidence, which with source validity witnesses admissibility *)
    preflight    : fresh_build_preflight_ok p
  }.
  Arguments MakeFacts {p core accepted} _ _.
  Arguments source_valid {p core accepted} _.
  Arguments preflight {p core accepted} _.
  Definition Facts {p : Syntax.Program} (core : Core p)
    (accepted : core_diagnostics core = nil) : Type := FactsRepresentation core accepted.

  Definition core_facts {p} (core : Core p) (Hnil : core_diagnostics core = nil)
    : Facts core Hnil :=
    let He : elaboration_diagnostics p (core_index core) = nil :=
      eq_trans (eq_sym (core_diagnostics_eq_elaboration core)) Hnil in
    MakeFacts
      (elaboration_no_diags_source_valid p (core_index core) He)
      (elaboration_no_diags_preflight p (core_index core) He).
End AcceptedFacts.
Include AcceptedFacts.

(** each projection takes the accepted value only to fix its core, then reads that exact core *)
Definition expression_facts {p} {core : Core p} {acc} (_ : Facts core acc)
  : ExpressionFactTable p (core_indexed core) :=
  expression_facts_table (phase_fact_table (phase core)).
Definition type_name_facts {p} {core : Core p} {acc} (_ : Facts core acc) : TypeNameFacts p :=
  phase_type_name_facts (phase core).
Definition facts_package_refs {p} {core : Core p} {acc} (_ : Facts core acc) := core_package_refs core.
(* each stated over [facts_package_refs] — the SAME map, spelled the way every consumer spells it. *)
Definition package_present {p} {core : Core p} {acc} (f : Facts core acc) : forall dir,
  PackageMap.In dir (facts_package_refs f) <-> list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true
  := core_package_present core.
Definition package_len {p} {core : Core p} {acc} (f : Facts core acc) : forall dir l,
  PackageMap.find dir (facts_package_refs f) = Some l -> length l = package_main_count dir (Syntax.files p)
  := core_package_len core.
Definition package_belongs {p} {core : Core p} {acc} (f : Facts core acc) : forall dir l,
  PackageMap.find dir (facts_package_refs f) = Some l -> forall d, In d l ->
  FilePath.parent (Index.Snapshot.file_ref_path (Index.Snapshot.node_ref_file (Index.erase_ref d))) = dir
  := core_package_belongs core.
Definition facts_root_layout {p} {core : Core p} {acc} (_ : Facts core acc) := core_layout core.
Definition facts_root_layout_ok {p} {core : Core p} {acc} (f : Facts core acc)
  : facts_root_layout f = root_layout p := core_layout_exact core.
Definition build_plan {p} {core : Core p} {acc} (_ : Facts core acc) := core_plan core.
Definition build_plan_ok {p} {core : Core p} {acc} (f : Facts core acc)
  : build_plan f = fresh_build_plan p := core_plan_is_fresh_build_plan core.

(** the public expression-fact query is total: on a valid result every typed reference has an entry *)
Lemma expression_ref_fact_some {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) :
  exists f, Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er))
              (fact_table_map (expression_facts facts)) = Some f.
Proof.
  assert (Hkind : Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Index.ExpressionKind)
    by exact (proj2_sig er).
  destruct (Index.kind_view_expr _ Hkind) as [e' Hv].
  pose proof (noderef_in_prog_visit p (Index.erase_ref er)) as Hin.
  pose proof (proj2 (Typing.program_typedb_iff predeclared_type p) (proj1 (source_valid facts))) as HPT.
  destruct (program_visit_const_info_some p HPT (Index.erase_ref er)
              (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) e' Hin Hv) as [ci Hci].
  pose proof (fact_table_complete (expression_facts facts) (Index.erase_ref er)
                (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) Hin) as Hfind.
  exists (MakeExpressionFact ci (occurrence_use_resolved (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)))).
  rewrite Hfind. exact (occurrence_expr_fact_status _ e' ci Hv Hci).
Qed.

Lemma expression_fact_at_not_none {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er)) (fact_table_map (expression_facts facts)) = None -> False.
Proof. intro Hn. destruct (expression_ref_fact_some facts er) as [f Hf]. rewrite Hf in Hn; discriminate. Qed.

(* the lookup discharges its [None] by the totality proof, so a defect-shipping option is impossible *)
Definition fact_of_find {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p)
  (o : option ExpressionFact) :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er)) (fact_table_map (expression_facts facts)) = o -> ExpressionFact :=
  match o with
  | Some f => fun _ => f
  | None   => fun Hn => False_rect ExpressionFact (expression_fact_at_not_none facts er Hn)
  end.

Definition expression_fact_at {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) : ExpressionFact :=
  fact_of_find facts er
    (Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er)) (fact_table_map (expression_facts facts)))
    eq_refl.

Lemma fact_of_find_some {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) o Ho f :
  o = Some f -> fact_of_find facts er o Ho = f.
Proof. intros ->. cbn. reflexivity. Qed.

(** the total query returns exactly what the sealed table holds, rather than a fresh value *)
Lemma expression_fact_at_find {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) f :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er)) (fact_table_map (expression_facts facts)) = Some f ->
  expression_fact_at facts er = f.
Proof.
  intro Hf. unfold expression_fact_at.
  exact (fact_of_find_some facts er
    (Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref er)) (fact_table_map (expression_facts facts)))
    eq_refl f Hf).
Qed.

(** the public type-name query is total and needs no validity, since a conversion's name resolves always *)
Lemma type_name_ref_fact_some {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) :
  exists f, Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr))
              (type_name_map (type_name_facts facts)) = Some f.
Proof.
  assert (Hkind : Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr)) = Index.TypeNameKind)
    by exact (proj2_sig tr).
  destruct (Index.kind_view_typename _ Hkind) as [ts Hv].
  pose proof (noderef_in_prog_visit p (Index.erase_ref tr)) as Hin.
  pose proof (type_name_complete (type_name_facts facts) (Index.erase_ref tr)
                (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr)) Hin) as Hfind.
  exists (MakeTypeNameFact (predeclared_type ts)).
  rewrite Hfind. exact (occurrence_type_name_fact_some _ ts Hv).
Qed.

Lemma type_name_fact_at_not_none {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map (type_name_facts facts)) = None -> False.
Proof. intro Hn. destruct (type_name_ref_fact_some facts tr) as [f Hf]. rewrite Hf in Hn; discriminate. Qed.

Definition type_name_fact_of_find {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p)
  (o : option TypeNameFact) :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map (type_name_facts facts)) = o -> TypeNameFact :=
  match o with
  | Some f => fun _ => f
  | None   => fun Hn => False_rect TypeNameFact (type_name_fact_at_not_none facts tr Hn)
  end.

Definition type_name_fact_at {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) : TypeNameFact :=
  type_name_fact_of_find facts tr
    (Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map (type_name_facts facts)))
    eq_refl.

Lemma type_name_fact_of_find_some {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) o Ho f :
  o = Some f -> type_name_fact_of_find facts tr o Ho = f.
Proof. intros ->. cbn. reflexivity. Qed.

(** the total type-name query returns what the sealed table holds, and never re-resolves *)
Lemma type_name_fact_at_find {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) f :
  Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map (type_name_facts facts)) = Some f ->
  type_name_fact_at facts tr = f.
Proof.
  intro Hf. unfold type_name_fact_at.
  exact (type_name_fact_of_find_some facts tr
    (Index.KeyMap.find (Index.Snapshot.node_ref_key (Index.erase_ref tr)) (type_name_map (type_name_facts facts)))
    eq_refl f Hf).
Qed.

(** the stored fact is the resolution of the source name recovered through the reference *)
Theorem type_name_fact_at_resolves {p} {core : Core p} {acc} (facts : Facts core acc) (tr : Index.TypeNameRef p) ts :
  Index.type_name_ref_syntax tr = Some ts ->
  type_name_fact_at facts tr = MakeTypeNameFact (predeclared_type ts).
Proof.
  intro Hts. unfold Index.type_name_ref_syntax in Hts.
  pose proof (noderef_in_prog_visit p (Index.erase_ref tr)) as Hin.
  pose proof (type_name_complete (type_name_facts facts) (Index.erase_ref tr)
                (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref tr)) Hin) as Hfind.
  rewrite (occurrence_type_name_fact_some _ ts Hts) in Hfind.
  exact (type_name_fact_at_find facts tr _ Hfind).
Qed.

(** two conversions to one source name at distinct occurrences obtain distinct target references *)
Theorem repeated_name_distinct_refs {p} {core : Core p} {acc} (facts : Facts core acc)
    (r1 : Index.Snapshot.NodeRef p) occ1 (er1 : Index.ExprRef p) x1
    (r2 : Index.Snapshot.NodeRef p) occ2 (er2 : Index.ExprRef p) x2 :
  let idx := core_index core in
  In (r1, occ1) (program_visit p) -> Index.view_expr occ1 = Some (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) x1) ->
    Index.as_expr idx r1 = Some er1 ->
  In (r2, occ2) (program_visit p) -> Index.view_expr occ2 = Some (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) x2) ->
    Index.as_expr idx r2 = Some er2 ->
  Index.Snapshot.node_ref_key r1 <> Index.Snapshot.node_ref_key r2 ->
  exists tr1 tr2,
    conversion_target_ref idx er1 = Some tr1 /\ conversion_target_ref idx er2 = Some tr2
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr1) <> Index.Snapshot.node_ref_key (Index.erase_ref tr2)
    /\ Index.type_name_ref_syntax tr1 = Index.type_name_ref_syntax tr2
    /\ type_name_fact_at facts tr1 = type_name_fact_at facts tr2.
Proof.
  intros idx Hin1 Hv1 Ha1 Hin2 Hv2 Ha2 Hne.
  destruct (conversion_target_ref_conv idx r1 occ1 er1 (Syntax.type_expr_of_name Names.Uint8) x1 Hin1 Hv1 Ha1) as [tr1 [Hc1 [Hk1 [_ Hs1]]]].
  destruct (conversion_target_ref_conv idx r2 occ2 er2 (Syntax.type_expr_of_name Names.Uint8) x2 Hin2 Hv2 Ha2) as [tr2 [Hc2 [Hk2 [_ Hs2]]]].
  exists tr1, tr2. split; [exact Hc1 | split; [exact Hc2 | split; [ | split ]]].
  - intro Heq. apply Hne. rewrite Hk1, Hk2 in Heq. exact (type_name_key_inj r1 r2 Heq).
  - rewrite Hs1, Hs2. reflexivity.
  - rewrite (type_name_fact_at_resolves facts tr1 _ Hs1), (type_name_fact_at_resolves facts tr2 _ Hs2). reflexivity.
Qed.

(** on SUCCESS each package's bucket is a singleton (length = main count = 1). *)
Lemma package_singleton {p} {core : Core p} {acc} (facts : Facts core acc) dir l :
  PackageMap.find dir (facts_package_refs facts) = Some l -> exists d, l = [d].
Proof.
  intro E. pose proof (package_len facts dir l E) as Hlen.
  assert (Hmem : list_dir_mem dir (Syntax.file_bindings (Syntax.files p)) = true).
  { apply (package_present facts dir). apply PackageFacts.in_find_iff. rewrite E. discriminate. }
  assert (Hmt : PackageMap.MapsTo dir (MakePackageSummary (package_main_count dir (Syntax.files p))) (package_summaries (Syntax.files p))).
  { apply PackageFacts.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (proj1 (current_package_rules_exactly_one p) (proj2 (source_valid facts)) dir _ Hmt) as Hone. cbn [summary_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(** the public package-main query projects the retained singleton bucket, never a recomputed index *)
Definition package_main_at {p} {core : Core p} {acc} (facts : Facts core acc) (r : PackageRef p) : Index.DeclRef p.
Proof.
  remember (PackageMap.find (package_ref_key r) (facts_package_refs facts)) as o eqn:E.
  destruct o as [l|].
  - destruct l as [|d rest].
    + exfalso. destruct (package_singleton facts (package_ref_key r) [] (eq_sym E)) as [d Hd]; discriminate Hd.
    + exact d.
  - exfalso.
    assert (Hin : PackageMap.In (package_ref_key r) (facts_package_refs facts))
      by (apply (package_present facts), (package_ref_ok r)).
    apply PackageFacts.in_find_iff in Hin. exact (Hin (eq_sym E)).
Defined.

(** the decision is about one retained core, so an equal recomputed core cannot substitute for it *)


Definition elaboration_indexed {p} (pe : Elaboration p) : Index.Program p := core_indexed (elaboration_core pe).



(** the one elaboration pass: the shared collections are computed once and feed both the decision and the facts *)
Theorem core_seals_tnfacts {p} (core : Core p) (Hnil : core_diagnostics core = nil) :
  type_name_facts (core_facts core Hnil) = phase_type_name_facts (phase core).
Proof. reflexivity. Qed.

Theorem core_seals_facts {p} (core : Core p) (Hnil : core_diagnostics core = nil) :
  expression_facts (core_facts core Hnil) = expression_facts_table (phase_fact_table (phase core)).
Proof. reflexivity. Qed.



(** elaboration exposes facts exactly on admissible programs, and diagnostics exactly otherwise *)
Theorem elaboration_accepted_iff_admissible (p : Syntax.Program) :
  core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p.
Proof.
  rewrite (core_diagnostics_eq_elaboration (elaboration_core (elaborate p))).
  exact (elaboration_diagnostics_nil_iff_admissible p
           (core_index (elaboration_core (elaborate p)))).
Qed.

Theorem elaboration_rejected_iff_inadmissible (p : Syntax.Program) :
  core_diagnostics (elaboration_core (elaborate p)) <> nil <-> ~ Admissible p.
Proof.
  split; intro H.
  - intro Hv. exact (H (proj2 (elaboration_accepted_iff_admissible p) Hv)).
  - intro He. exact (H (proj1 (elaboration_accepted_iff_admissible p) He)).
Qed.

(** the capability retains its core *)
Module Type CAPABILITY.
  Parameter Program : Type.
  Parameter source   : Program -> Syntax.Program.
  Parameter core     : forall cp : Program, Core (source cp).   (* THE retained whole elaboration *)
  Parameter accepted : forall cp : Program, core_diagnostics (core cp) = nil.

  Parameter Failure : Syntax.Program -> Type.
  Parameter failure_core : forall {p}, Failure p -> Core p.
  Parameter rejected : forall {p} (fail : Failure p), core_diagnostics (failure_core fail) <> nil.

  (* the outcome is transparent but both payloads are not, so no constructor takes foreign data *)
  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (fail : Failure p).

  (* the one exported mint; the internal one and its argument are sealed, so no client reaches it *)
  Parameter compile : forall p : Syntax.Program, Outcome p.
  (* neither decision fact names a builder, so neither can recover a retained object by rebuilding a peer *)
  Parameter compile_complete : forall p, Admissible p ->
    exists cp Hcp, compile p = Compiled p cp Hcp.
  Parameter compile_rejected_of_inadmissible : forall p, ~ Admissible p ->
    exists fail, compile p = Rejected p fail.
End CAPABILITY.

Module Capability : CAPABILITY.
  Record ProgramRepresentation : Type := MakeProgram {
    source : Syntax.Program;
    core    : Core source;
    accepted     : core_diagnostics core = nil
  }.
  Definition Program : Type := ProgramRepresentation.

  Record FailureRepresentation (p : Syntax.Program) : Type := MakeFailure {
    failure_core : Core p ;
    rejected     : core_diagnostics failure_core <> nil
  }.
  Arguments MakeFailure {p} _ _.
  Arguments failure_core {p} _.
  Arguments rejected {p} _.
  Definition Failure (p : Syntax.Program) : Type := FailureRepresentation p.

  Definition minted (p : Syntax.Program) (a : Elaboration p)
    : { cp : Program | source cp = p } + Failure p :=
    match decision a with
    | AcceptedDecision Hnil => inl (exist _ (MakeProgram p (elaboration_core a) Hnil) eq_refl)
    | RejectedDecision Hne  => inr (MakeFailure (elaboration_core a) Hne)
    end.

  Lemma minted_accepted : forall p (a : Elaboration p),
    core_diagnostics (elaboration_core a) = nil -> exists s, minted p a = inl s.
  Proof.
    intros p a Hnil. unfold minted. destruct (decision a) as [H|Hne].
    - eexists; reflexivity.
    - exfalso; exact (Hne Hnil).
  Qed.

  Lemma minted_rejected : forall p (a : Elaboration p),
    core_diagnostics (elaboration_core a) <> nil ->
    exists fail, minted p a = inr fail /\ failure_core fail = elaboration_core a.
  Proof.
    intros p a Hne. unfold minted. destruct (decision a) as [Hnil|H].
    - exfalso; exact (Hne Hnil).
    - eexists; split; reflexivity.
  Qed.

  Lemma minted_retains : forall p (a : Elaboration p) s, minted p a = inl s ->
    eq_rect (source (proj1_sig s)) Core (core (proj1_sig s)) p (proj2_sig s) = elaboration_core a.
  Proof.
    intros p a s E. unfold minted in E. destruct (decision a) as [Hnil|Hne].
    - injection E as <-. reflexivity.
    - discriminate E.
  Qed.

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (fail : Failure p).

  (** the compiler reads the retained decision and passes the core through, so success needs no equality *)
  Definition outcome_of_elaboration (p : Syntax.Program) (a : Elaboration p) : Outcome p :=
    match minted p a with
    | inl s    => Compiled p (proj1_sig s) (proj2_sig s)
    | inr fail => Rejected p fail
    end.

  Definition compile (p : Syntax.Program) : Outcome p :=
    outcome_of_elaboration p (elaborate p).

  Lemma compile_complete : forall p, Admissible p ->
    exists cp Hcp, compile p = Compiled p cp Hcp.
  Proof.
    intros p Hv.
    destruct (minted_accepted p (elaborate p)
                (proj2 (elaboration_accepted_iff_admissible p) Hv)) as [s Hs].
    exists (proj1_sig s), (proj2_sig s).
    unfold compile, outcome_of_elaboration. rewrite Hs. reflexivity.
  Qed.

  Lemma compile_rejected_of_inadmissible : forall p, ~ Admissible p ->
    exists fail, compile p = Rejected p fail.
  Proof.
    intros p Hnv.
    destruct (minted_rejected p (elaborate p)
                (proj2 (elaboration_rejected_iff_inadmissible p) Hnv)) as [fail [Hm _]].
    exists fail. unfold compile, outcome_of_elaboration. rewrite Hm. reflexivity.
  Qed.

End Capability.
Include Capability.
Arguments Compiled {p} _ _.
Arguments Rejected {p} _.

(* every public component is a projection of the retained core — never a re-elaboration. *)
Definition program_index (cp : Program) : Index.Program (source cp) := core_indexed (core cp).
Definition program_input (cp : Program) : Input (source cp) := core_input (core cp).
Definition program_phase (cp : Program) : Phase (program_input cp) := phase (core cp).
Definition facts (cp : Program) : Facts (core cp) (accepted cp) :=
  core_facts (core cp) (accepted cp).

Definition admissible (cp : Program) : Admissible (source cp) :=
  conj (preflight (facts cp))
       (source_valid (facts cp)).

(** the capability's phase and tables are the retained core's own, all by reflexivity *)
Theorem compilable_retains_phase : forall cp : Program, program_phase cp = phase (core cp).
Proof. reflexivity. Qed.

Theorem compilable_retains_expr_facts : forall cp : Program,
  expression_facts (facts cp) = expression_facts_table (phase_fact_table (program_phase cp)).
Proof. reflexivity. Qed.

Theorem compilable_retains_tnfacts : forall cp : Program,
  type_name_facts (facts cp) = phase_type_name_facts (program_phase cp).
Proof. reflexivity. Qed.

(** both queries project the same package object the decision used, each from its own retained core *)
Theorem accepted_package_refs_are_decision_refs : forall cp : Program,
  facts_package_refs (facts cp) = core_package_refs (core cp).
Proof. reflexivity. Qed.

(** the compiled evidence exposes that the same program types, as a projection rather than a copy *)
Theorem compile_program_typed : forall p, Admissible p -> Typing.Program predeclared_type p.
Proof. intros p H; exact (proj1 (proj2 H)). Qed.

Theorem compilable_program_typed : forall cp : Program, Typing.Program predeclared_type (source cp).
Proof. intro cp; exact (compile_program_typed _ (admissible cp)). Qed.

(** a returned failure retains the core that produced it, not a copied diagnostic list *)
Definition failure_diagnostics {p} (fail : Failure p) : list (DiagnosticReason p) :=
  core_diagnostics (failure_core fail).
Definition failure_nonempty {p} (fail : Failure p) : failure_diagnostics fail <> nil := rejected fail.

(* the rejected elaboration, projected — the whole causal chain a diagnostic consumer needs. *)
Definition failure_input {p} (fail : Failure p) : Input p := core_input (failure_core fail).
Definition failure_phase {p} (fail : Failure p) : Phase (failure_input fail) := phase (failure_core fail).
Definition failure_index {p} (fail : Failure p) : Index.Snapshot.Syntax p := core_index (failure_core fail).
Definition failure_indexed {p} (fail : Failure p) : Index.Program p := core_indexed (failure_core fail).
Definition failure_package_refs {p} (fail : Failure p) := core_package_refs (failure_core fail).
Definition failure_layout {p} (fail : Failure p) := core_layout (failure_core fail).
Definition failure_plan {p} (fail : Failure p) := core_plan (failure_core fail).
Definition failure_raw_diagnostics {p} (fail : Failure p) := core_raw_diagnostics (failure_core fail).

(** the rejected query projects the SAME package object the failed decision used — by [reflexivity]. *)
Theorem rejected_package_refs_are_decision_refs : forall p (fail : Failure p),
  failure_package_refs fail = core_package_refs (failure_core fail).
Proof. reflexivity. Qed.




(** compilation succeeds exactly on admissible programs, its success carrying its own validity *)
Theorem compile_ok_valid : forall p cp Hcp,
  compile p = Compiled cp Hcp -> source cp = p /\ Admissible (source cp).
Proof.
  intros p cp Hcp _. split; [ exact Hcp | exact (admissible cp) ].
Qed.

(** the source decision and the preflight decision together are exactly admissibility *)
Lemma compile_ok_of_source_spec_valid_b : forall p,
  source_spec_valid_b p = true -> fresh_build_disposition_ok (fresh_build_plan p) = true ->
  exists cp Hcp, compile p = Compiled cp Hcp.
Proof.
  intros p H Hpf. apply compile_complete. split.
  - unfold fresh_build_preflight_ok. exact Hpf.
  - apply (proj1 (source_spec_valid_b_iff p)); exact H.
Qed.

(** admissibility from the two decidable checks, which is the introduction the witnesses use *)
Lemma admissible_of_source_spec_valid_b : forall p,
  source_spec_valid_b p = true -> fresh_build_disposition_ok (fresh_build_plan p) = true -> Admissible p.
Proof.
  intros p H Hpf. split.
  - unfold fresh_build_preflight_ok. exact Hpf.
  - apply (proj1 (source_spec_valid_b_iff p)); exact H.
Qed.

(** each diagnostic layer has its own emptiness characterization, and the two-branch structure is pinned *)
Theorem semantic_diagnostics_empty_iff_source_valid : forall p idx,
  semantic_diagnostics p idx = nil <-> SourceProgramValid p.
Proof.
  intros p idx. split.
  - intro H. apply (proj1 (semantic_ok_b_source_program_valid p)),
                   (proj1 (semantic_diagnostics_empty_iff p idx)); exact H.
  - intro H. apply (proj2 (semantic_diagnostics_empty_iff p idx)), (proj2 (semantic_ok_b_source_program_valid p)); exact H.
Qed.

(** the sole-package plan expressed exactly (iota over the singleton [selected_package_keys]). *)
Lemma fresh_build_plan_of_sole : forall p dir,
  selected_package_keys p = [dir] ->
  fresh_build_plan p = WriteSingleMain dir (package_import_path (Syntax.module_spec p) dir)
                          (default_exec_name (Syntax.module_spec p) dir)
                          (PackageMap.find (default_exec_name (Syntax.module_spec p) dir) (root_layout p)).
Proof. intros p dir Hk. unfold fresh_build_plan. rewrite Hk. reflexivity. Qed.

(** a failed preflight makes the fresh-build report exactly one build-output diagnostic *)
Lemma fresh_build_diagnostics_fail_singleton : forall p,
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  exists pk name, fresh_build_diagnostics p = [BuildOutputIsDirectory pk name].
Proof.
  intros p Hpf. destruct (proj1 (preflight_fails_iff p) Hpf) as [dir [Hk Hfind]].
  destruct (sole_package_ref_some p dir (sole_package_present p dir Hk)) as [pk Hpk].
  exists pk. exists (default_exec_name (Syntax.module_spec p) dir).
  unfold fresh_build_diagnostics, fresh_build_diagnostics_of. rewrite (fresh_build_plan_of_sole p dir Hk), Hfind, Hpk. reflexivity.
Qed.

(** the command-facing report inherits that precedence, hiding every semantic diagnostic *)
Theorem elaboration_diagnostics_fresh_failure : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  exists pk name, elaboration_diagnostics p idx = [BuildOutputIsDirectory pk name].
Proof.
  intros p idx Hpf. rewrite (elaboration_diagnostics_eq_fresh p idx Hpf).
  apply (fresh_build_diagnostics_fail_singleton p Hpf).
Qed.


(** the capability holds the exact core, and the plan is retained by derivation from it *)
Definition program_build_plan (cp : Program) : FreshBuildDisposition :=
  build_plan (facts cp).

Definition program_root_layout (cp : Program) : PackageMap.t FreshRootEntryKind :=
  facts_root_layout (facts cp).

(** the plan and layout are projections whose coherence the elaboration carried, not a recomputation *)
Lemma program_build_plan_retained : forall cp, program_build_plan cp = fresh_build_plan (source cp).
Proof. intro cp. exact (build_plan_ok (facts cp)). Qed.

Lemma program_root_layout_retained : forall cp, program_root_layout cp = root_layout (source cp).
Proof. intro cp. exact (facts_root_layout_ok (facts cp)). Qed.

(** exactly one path mints a capability: the extractor inspects the compiler's own outcome *)
Lemma compile_rejected_not_admissible (p : Syntax.Program) (fail : Failure p) :
  compile p = Rejected fail -> ~ Admissible p.
Proof.
  intros E H. destruct (compile_complete p H) as [cp [Hcp Hc]].
  rewrite E in Hc. discriminate.
Qed.

Definition program_of_admissible (p : Syntax.Program) (H : Admissible p)
  : { cp : Program | source cp = p /\ exists Hcp, compile p = Compiled cp Hcp } :=
  match compile p as o return compile p = o -> _ with
  | Compiled cp Hs => fun E => exist _ cp (conj Hs (ex_intro _ Hs E))
  | Rejected fail  => fun E => False_rect _ (compile_rejected_not_admissible p fail E H)
  end eq_refl.

(** the capability, and the two facts every witness needs: it is the outcome, and its source is that program *)
Definition capability_of_admissible (p : Syntax.Program) (H : Admissible p) : Program :=
  proj1_sig (program_of_admissible p H).
Definition capability_source (p : Syntax.Program) (H : Admissible p)
  : source (capability_of_admissible p H) = p := proj1 (proj2_sig (program_of_admissible p H)).
Definition capability_is_compile_outcome (p : Syntax.Program) (H : Admissible p)
  : exists Hcp, compile p = Compiled (capability_of_admissible p H) Hcp
  := proj2 (proj2_sig (program_of_admissible p H)).

(** A rejected program yields no Program (and hence no Safe.Program, no image). *)
Lemma reject_no_compile : forall p, source_spec_valid_b p = false -> ~ Admissible p.
Proof.
  intros p E [_ Hsv].
  pose proof (proj2 (source_spec_valid_b_iff p) Hsv) as Hok.
  rewrite Hok in E; discriminate.
Qed.

(** admissibility depends only on the file map, never on construction order *)
Theorem source_program_valid_files_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> SourceProgramValid p1 -> SourceProgramValid p2.
Proof.
  intros p1 p2 Heq [Ht [Hdu Hme]]. split; [ exact (Typing.program_equal predeclared_type p1 p2 Heq Ht) |].
  assert (Hconv : forall dir s, PackageMap.MapsTo dir s (package_summaries (Syntax.files p2)) ->
                                PackageMap.MapsTo dir s (package_summaries (Syntax.files p1))).
  { intros dir s Hmt. apply PackageFacts.find_mapsto_iff.
    rewrite (package_summaries_equal (Syntax.files p1) (Syntax.files p2) Heq dir).
    apply PackageFacts.find_mapsto_iff. exact Hmt. }
  split; intros dir s Hmt; [ apply (Hdu dir s) | apply (Hme dir s) ]; apply Hconv; exact Hmt.
Qed.

Theorem source_spec_valid_files_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> source_spec_valid_b p1 = source_spec_valid_b p2.
Proof.
  intros p1 p2 Heq.
  destruct (source_spec_valid_b p1) eqn:E1; destruct (source_spec_valid_b p2) eqn:E2; try reflexivity.
  - apply (proj1 (source_spec_valid_b_iff p1)) in E1. apply (source_program_valid_files_equal p1 p2 Heq) in E1.
    apply (proj2 (source_spec_valid_b_iff p2)) in E1. rewrite E1 in E2; discriminate.
  - apply (proj1 (source_spec_valid_b_iff p2)) in E2. apply (source_program_valid_files_equal p2 p1 (Syntax.files_equal_sym _ _ Heq)) in E2.
    apply (proj2 (source_spec_valid_b_iff p1)) in E2. rewrite E2 in E1; discriminate.
Qed.

(** admissibility is decidable from the two source booleans, so no proof here names a builder *)
Lemma admissible_dec : forall p, {Admissible p} + {~ Admissible p}.
Proof.
  intro p. destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
  - destruct (source_spec_valid_b p) eqn:Epk.
    + left.  exact (admissible_of_source_spec_valid_b p Epk Ep).
    + right. exact (reject_no_compile p Epk).
  - right. intros [Hpf _]. unfold fresh_build_preflight_ok in Hpf. rewrite Hpf in Ep. discriminate Ep.
Qed.


(** determinism split correctly: the source facts follow the file map, the plan also the module spec *)
Theorem root_layout_input_equal : forall p1 p2,
  ProgramInputEqual p1 p2 -> root_layout p1 = root_layout p2.
Proof. intros p1 p2 H. exact (root_layout_equal _ _ (proj2 H)). Qed.

(* the whole-program corollary: equal inputs give an equal import path for any package directory *)
Theorem package_import_path_input_equal : forall p1 p2 dir,
  ProgramInputEqual p1 p2 ->
  package_import_path (Syntax.module_spec p1) dir = package_import_path (Syntax.module_spec p2) dir.
Proof. intros p1 p2 dir H. apply package_import_path_deterministic; [ exact (proj1 H) | reflexivity ]. Qed.

(** the ERASED final (command-facing) report: snapshot-free, comparable across programs by [=]. *)
Definition erased_elaboration_report (p : Syntax.Program) (idx : Index.Snapshot.Syntax p) : list ErasedDiagnostic :=
  map erase_diagnostic (elaboration_diagnostics p idx).

(** a failed preflight erases to one build-output diagnostic carrying the exact colliding name *)
Lemma erased_fresh_report_of_sole : forall p dir,
  selected_package_keys p = [dir] ->
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  map erase_diagnostic (fresh_build_diagnostics p)
    = [MakeErased CodeBuildOutputIsDirectory (AnchorPackage dir) [] None
         (Some (default_exec_name (Syntax.module_spec p) dir)) None].
Proof.
  intros p dir Hk Hpf.
  destruct (proj1 (preflight_fails_iff p) Hpf) as [dir' [Hk' Hfind]].
  assert (dir' = dir) as -> by (rewrite Hk in Hk'; congruence).
  unfold fresh_build_diagnostics, fresh_build_diagnostics_of. rewrite (fresh_build_plan_of_sole p dir Hk), Hfind.
  unfold sole_package_ref. destruct (Bool.bool_dec (package_present_b p dir) true) as [Ht|Hcon].
  - reflexivity.
  - exfalso. apply Hcon. exact (sole_package_present p dir Hk).
Qed.

(** equal program inputs give an equal erased final report, the preflight branch needing the module spec *)
Theorem erased_elaboration_report_input_equal : forall p1 p2 idx1 idx2,
  ProgramInputEqual p1 p2 ->
  erased_elaboration_report p1 idx1 = erased_elaboration_report p2 idx2.
Proof.
  intros p1 p2 idx1 idx2 H. pose proof (proj2 H) as Hf.
  unfold erased_elaboration_report, elaboration_diagnostics, command_diagnostics_of.
  rewrite (fresh_build_disposition_input_equal _ _ H).
  destruct (fresh_build_disposition_ok (fresh_build_plan p2)) eqn:Ed.
  - exact (erased_report_files_equal p1 p2 idx1 idx2 Hf).
  - assert (Ed1 : fresh_build_disposition_ok (fresh_build_plan p1) = false)
      by (rewrite (fresh_build_disposition_input_equal _ _ H); exact Ed).
    destruct (proj1 (preflight_fails_iff p1) Ed1) as [dir [Hk1 _]].
    assert (Hk2 : selected_package_keys p2 = [dir])
      by (rewrite <- (selected_package_keys_equal _ _ Hf); exact Hk1).
    fold (fresh_build_diagnostics p1) (fresh_build_diagnostics p2).
    rewrite (erased_fresh_report_of_sole p1 dir Hk1 Ed1),
            (erased_fresh_report_of_sole p2 dir Hk2 Ed).
    (* the erased build-output NAME is [default_exec_name], a function of the ModuleSpec (equal by inputs). *)
    rewrite (proj1 H). reflexivity.
Qed.

(** the empty program is accepted vacuously: no package to type and no main to count *)
Lemma source_spec_valid_b_empty : forall ms, source_spec_valid_b (empty_program ms) = true.
Proof. intro ms. vm_compute. reflexivity. Qed.

(** the live factored-root empty surface, with its decidable companions *)
Theorem source_program_valid_empty : forall ms, SourceProgramValid (empty_program ms).
Proof.
  intro ms. apply (proj1 (source_spec_valid_b_iff (empty_program ms))). apply source_spec_valid_b_empty.
Qed.

(** an out-of-range argument rejects the whole program before any emission *)
Definition over_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral (Z.to_N (Integer.platform_maximum + 1)) ] ] ].

(* rejection happens in Rocq, so there is no capability and therefore no image and no bytes *)
Example over_program_untyped   : program_typedb over_program = false.        Proof. vm_compute; reflexivity. Qed.
Example over_program_not_valid    : source_spec_valid_b over_program = false.               Proof. vm_compute; reflexivity. Qed.
Example over_program_rejected  : exists fail, compile over_program = Rejected fail.
Proof. exact (compile_rejected_of_inadmissible over_program
                (reject_no_compile over_program over_program_not_valid)). Qed.
Example over_program_report : map erased_code (erased_report over_program
                                (Index.Snapshot.index_program over_program)) = [CodeDefaultNotRepresentable].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Example over_program_no_compile : ~ Admissible over_program.
Proof. exact (reject_no_compile over_program over_program_not_valid). Qed.

(* the rejected side on a concrete program, stated over the returned failure's own retained core *)
Theorem over_program_failure_retains_rejected_core :
  exists fail,
    compile over_program = Rejected fail
    (* the exposed diagnostics ARE the retained core's own — definitionally, not a copied list *)
    /\ failure_diagnostics fail = core_diagnostics (failure_core fail)
    /\ failure_diagnostics fail <> nil.
Proof.
  destruct (compile_rejected_of_inadmissible over_program over_program_no_compile) as [fail Hc].
  exists fail. split; [ exact Hc | split; [ reflexivity | exact (failure_nonempty fail) ] ].
Qed.

(** an integer program compiles; an invalid nested conversion rejects the whole program before any bytes *)
Definition int_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 127)
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral 18446744073709551615)
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127)) ] ] ].
Example int_program_typed    : program_typedb int_program = true. Proof. vm_compute; reflexivity. Qed.
Example int_program_ok       : source_spec_valid_b int_program = true.        Proof. vm_compute; reflexivity. Qed.
Example int_program_compiles : exists cp Hcp, compile int_program = Compiled cp Hcp.
Proof. exact (compile_ok_of_source_spec_valid_b _ int_program_ok ltac:(vm_compute; reflexivity)). Qed.

(** a valid inner conversion whose value does not fit the outer one cannot be revived *)
Definition bad_convert_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.IntegerLiteral 300)) ] ] ].
Example bad_convert_untyped     : program_typedb bad_convert_program = false. Proof. vm_compute; reflexivity. Qed.
Example bad_convert_rejected    : exists fail, compile bad_convert_program = Rejected fail.
Proof. exact (compile_rejected_of_inadmissible bad_convert_program
                (reject_no_compile bad_convert_program eq_refl)). Qed.
Example bad_convert_report : map erased_code (erased_report bad_convert_program
                               (Index.Snapshot.index_program bad_convert_program)) = [CodeInvalidConversion].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Example bad_convert_no_compile  : ~ Admissible bad_convert_program.
Proof. exact (reject_no_compile bad_convert_program eq_refl). Qed.

(** a string program mixing a literal with a bool and an int is typed and compiles *)
Definition str_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.StringLiteral "hello"; Syntax.BoolLiteral true; Syntax.IntegerLiteral 7 ] ] ].
Example str_program_typed    : program_typedb str_program = true. Proof. vm_compute; reflexivity. Qed.
Example str_program_ok       : source_spec_valid_b str_program = true.        Proof. vm_compute; reflexivity. Qed.
Example str_program_compiles : exists cp Hcp, compile str_program = Compiled cp Hcp.
Proof. exact (compile_ok_of_source_spec_valid_b _ str_program_ok ltac:(vm_compute; reflexivity)). Qed.

(** a float program compiles; a fractional float-to-integer conversion rejects the whole program *)
Definition float_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.FloatLiteral (Float.MakeDecimal 15 (-1) eq_refl)
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral (Float.MakeDecimal 15 (-1) eq_refl))
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral (Float.MakeDecimal 3 0 eq_refl)) ] ] ].
Example float_program_typed    : program_typedb float_program = true. Proof. vm_compute. reflexivity. Qed.
Example float_program_ok       : source_spec_valid_b float_program = true.        Proof. vm_compute. reflexivity. Qed.
Example float_program_compiles : exists cp Hcp, compile float_program = Compiled cp Hcp.
Proof. exact (compile_ok_of_source_spec_valid_b _ float_program_ok ltac:(vm_compute; reflexivity)). Qed.

Definition float_reject_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral (Float.MakeDecimal 35 (-1) eq_refl)) ] ] ].   (* int(3.5): fractional *)
Example float_reject_untyped    : program_typedb float_reject_program = false. Proof. vm_compute. reflexivity. Qed.
Example float_reject_rejected   : exists fail, compile float_reject_program = Rejected fail.
Proof. apply compile_rejected_of_inadmissible.
       apply (reject_no_compile float_reject_program); vm_compute; reflexivity. Qed.
Example float_reject_report : map erased_code (erased_report float_reject_program
                                (Index.Snapshot.index_program float_reject_program)) = [CodeInvalidConversion].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Example float_reject_no_compile : ~ Admissible float_reject_program.
Proof. apply (reject_no_compile float_reject_program); vm_compute; reflexivity. Qed.

(** a complex program compiles; an overflowing component and a nonzero imaginary each reject *)
Definition complex_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal (-25) (-1) eq_refl))
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Complex64)  (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal 0 0 eq_refl)))
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal 0 0 eq_refl)))
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Complex64)  (Syntax.IntegerLiteral 1)
                       ; Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 3 0 eq_refl) (Float.MakeDecimal 0 0 eq_refl))) ] ] ].
Example complex_program_typed    : program_typedb complex_program = true. Proof. vm_compute. reflexivity. Qed.
Example complex_program_ok       : source_spec_valid_b complex_program = true.        Proof. vm_compute. reflexivity. Qed.
Example complex_program_compiles : exists cp Hcp, compile complex_program = Compiled cp Hcp.
Proof. exact (compile_ok_of_source_spec_valid_b _ complex_program_ok ltac:(vm_compute; reflexivity)). Qed.

Definition complex_overflow_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 1 39 eq_refl) (Float.MakeDecimal 0 0 eq_refl))) ] ] ].
Example complex_overflow_untyped    : program_typedb complex_overflow_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_overflow_rejected   : exists fail, compile complex_overflow_program = Rejected fail.
Proof. apply compile_rejected_of_inadmissible.
       apply (reject_no_compile complex_overflow_program); vm_compute; reflexivity. Qed.
Example complex_overflow_report : map erased_code (erased_report complex_overflow_program
                                    (Index.Snapshot.index_program complex_overflow_program)) = [CodeInvalidConversion].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Example complex_overflow_no_compile : ~ Admissible complex_overflow_program.
Proof. apply (reject_no_compile complex_overflow_program); vm_compute; reflexivity. Qed.

Definition complex_nonzero_imag_program : Syntax.Program :=
  singleton_program
    (Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23)
    (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 3 0 eq_refl) (Float.MakeDecimal 1 0 eq_refl))) ] ] ].
Example complex_nonzero_imag_untyped    : program_typedb complex_nonzero_imag_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_rejected   : exists fail, compile complex_nonzero_imag_program = Rejected fail.
Proof. apply compile_rejected_of_inadmissible.
       apply (reject_no_compile complex_nonzero_imag_program); vm_compute; reflexivity. Qed.
Example complex_nonzero_imag_report : map erased_code (erased_report complex_nonzero_imag_program
                                        (Index.Snapshot.index_program complex_nonzero_imag_program)) = [CodeInvalidConversion].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_no_compile : ~ Admissible complex_nonzero_imag_program.
Proof. apply (reject_no_compile complex_nonzero_imag_program); vm_compute; reflexivity. Qed.

(** the index is sealed, so a fixture proves its report through the theorems rather than by computing *)

Definition c3_ms : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Version.Go1_23.

(** a permuted construction gives a byte-identical report, class and fact enumeration *)
Definition rnode_a : Syntax.FileNode := main_file_node (FilePath.Make "a.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ] ].
Definition rnode_b : Syntax.FileNode := main_file_node (FilePath.Make "b.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ] ].

Example reorder_builds1 : exists p, build_program c3_ms [rnode_a; rnode_b] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.
Example reorder_builds2 : exists p, build_program c3_ms [rnode_b; rnode_a] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.

Theorem reorder_construction_deterministic :
  forall p1 p2 (idx1 : Index.Snapshot.Syntax p1) (idx2 : Index.Snapshot.Syntax p2),
    build_program c3_ms [rnode_a; rnode_b] = Some p1 ->
    build_program c3_ms [rnode_b; rnode_a] = Some p2 ->
    erased_report p1 idx1 = erased_report p2 idx2
    /\ Index.KeyMap.elements (program_expr_facts p1) = Index.KeyMap.elements (program_expr_facts p2).
Proof.
  intros p1 p2 idx1 idx2 H1 H2.
  assert (HIE : ProgramInputEqual p1 p2).
  { unfold build_program in H1, H2.
    destruct (Syntax.files_of_nodes [rnode_a; rnode_b]) as [fm1|] eqn:F1; [ | discriminate ].
    destruct (Syntax.files_of_nodes [rnode_b; rnode_a]) as [fm2|] eqn:F2; [ | discriminate ].
    injection H1 as <-. injection H2 as <-. split; [ reflexivity | cbn [Syntax.files] ].
    exact (Syntax.files_of_nodes_permutation _ _ fm1 fm2 (perm_swap rnode_b rnode_a []) F1 F2). }
  pose proof (proj2 HIE) as HFE.
  split; [ exact (erased_report_files_equal p1 p2 idx1 idx2 HFE)
         | exact (program_expr_facts_enum_files_equal p1 p2 HFE) ].
Qed.

(** the module-only program is accepted with an empty report and an empty fact enumeration *)
Theorem empty_program_report :
  erased_report (empty_program c3_ms) (Index.Snapshot.index_program (empty_program c3_ms)) = nil
  /\ Index.KeyMap.elements (program_expr_facts (empty_program c3_ms)) = nil.
Proof.
  split.
  - apply (proj2 (erased_report_empty_iff (empty_program c3_ms) _)).
    rewrite semantic_ok_b_source_spec_valid_b. apply source_spec_valid_b_empty.
  - vm_compute. reflexivity.
Qed.

(** a nested invalid conversion is rejected, each diagnostic carrying a genuine strict-ancestor context *)
Definition nested_conv_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128)) ] ] ].

Example nested_conv_untyped : program_typedb nested_conv_program = false.
Proof. vm_compute. reflexivity. Qed.

(* the exact report: one invalid-conversion diagnostic, anchored at the inner conversion *)
Theorem nested_conv_erased_report :
  erased_report nested_conv_program (Index.Snapshot.index_program nested_conv_program)
  = [ MakeErased CodeInvalidConversion
        (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 7%positive))
        [ AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive) ]
        (Some (Typing.IntegerType Integer.Int8)) None (Some (Syntax.type_expr_of_name Names.Int8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** three mains in one package are rejected, each diagnostic naming a strictly later distinct main *)
Definition three_main_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ]; Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ]; Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 3 ] ] ].

(* the exact report: two redeclarations, each related to the first canonical main *)
Theorem three_main_erased_report :
  erased_report three_main_program (Index.Snapshot.index_program three_main_program)
  = [ MakeErased CodeMainRedeclared
        (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 6%positive))
        [ AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 3%positive) ] None None None
    ; MakeErased CodeMainRedeclared
        (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 9%positive))
        [ AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 3%positive) ] None None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** a package with no main is rejected, its diagnostic anchoring a genuinely represented package *)
Definition missing_main_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ ].

(* the exact report: one missing-main diagnostic at a package anchor, never at a fake node *)
Theorem missing_main_erased_report :
  erased_report missing_main_program (Index.Snapshot.index_program missing_main_program)
  = [ MakeErased CodeMissingMainEntry (AnchorPackage "") [] None None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** on any valid result every reference's queried fact is its occurrence's exact source-derived fact *)
Lemma expression_fact_at_exact {p} {core : Core p} {acc} (facts : Facts core acc) (er : Index.ExprRef p) :
  exists e ci,
    Index.view_expr (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Some e
    /\ constant_info e = Some ci
    /\ expression_fact_at facts er
       = MakeExpressionFact ci (occurrence_use_resolved (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er))).
Proof.
  assert (Hkind : Index.occurrence_kind (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) = Index.ExpressionKind)
    by exact (proj2_sig er).
  destruct (Index.kind_view_expr _ Hkind) as [e Hv].
  pose proof (noderef_in_prog_visit p (Index.erase_ref er)) as Hin.
  pose proof (proj2 (Typing.program_typedb_iff predeclared_type p) (proj1 (source_valid facts))) as HPT.
  destruct (program_visit_const_info_some p HPT (Index.erase_ref er)
              (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) e Hin Hv) as [ci Hci].
  pose proof (fact_table_complete (expression_facts facts) (Index.erase_ref er)
                (Index.Snapshot.source_occurrence_of_ref (Index.erase_ref er)) Hin) as Hfind.
  rewrite (occurrence_expr_fact_status _ e ci Hv Hci) in Hfind.
  exists e, ci. split; [exact Hv | split; [exact Hci | exact (expression_fact_at_find facts er _ Hfind)]].
Qed.

Definition fact_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.IntegerLiteral 5)) ] ] ].
Example fact_program_ok : source_spec_valid_b fact_program = true. Proof. vm_compute. reflexivity. Qed.

(** the exact per-occurrence facts of a valid nested conversion, projected to locals and values *)
Theorem fact_program_facts_exact :
  map (fun kv => (Index.key_local (fst kv),
                  match const_status (snd kv) with Typing.UntypedInfo _ => None | Typing.TypedInfo t _ => Some t end,
                  resolved_type_at (snd kv)))
      (Index.KeyMap.elements (program_expr_facts fact_program))
  = [ (5%positive, Some (Typing.FloatType F64), Some (Typing.FloatType F64))
    ; (7%positive, Some (Typing.IntegerType Integer.Int), None)
    ; (9%positive, None, None) ].
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the inner literal stays untyped and the inner conversion is typed, both unresolved as operands *)
Theorem fact_program_inner_literal :
  Index.KeyMap.find (Index.MakeKey (FilePath.Make "main.go" eq_refl) 9%positive) (program_expr_facts fact_program)
  = Some (MakeExpressionFact (Typing.UntypedInfo (Typing.IntegerConstant 5)) None).
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

Theorem fact_program_inner_conversion :
  Index.KeyMap.find (Index.MakeKey (FilePath.Make "main.go" eq_refl) 7%positive) (program_expr_facts fact_program)
  = Some (MakeExpressionFact (Typing.TypedInfo (Typing.IntegerType Integer.Int) (Typing.TypedInteger Integer.Int 5 eq_refl)) None).
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the outer argument's exact resolved constant is the rational five at float64, not merely some float *)
Theorem fact_program_outer_arg :
  option_map (fun f =>
     (match const_status f with Typing.TypedInfo t _ => Some t | Typing.UntypedInfo _ => None end,
      resolved_type_at f,
      match resolved_constant_at f with Some (Typing.FloatConstant fc) => Some (Float.numerator fc, Float.denominator fc) | _ => None end,
      match use_resolved f with Some _ => true | None => false end))
     (Index.KeyMap.find (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive) (program_expr_facts fact_program))
  = Some (Some (Typing.FloatType F64), Some (Typing.FloatType F64), Some (5%Z, 1%positive), true).
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the outer argument's complete fact: its proof-carrying typed constant and its exact resolved value *)
Theorem fact_program_outer_fact :
  Index.KeyMap.find (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive) (program_expr_facts fact_program)
  = Some {| const_status :=
              Typing.TypedInfo (Typing.FloatType F64)
                (Typing.TypedFloat F64
                   {| Float.exact := {| Float.numerator := 5; Float.denominator := 1; Float.canonical := Float.reduce_well_formed 5629499534213120 1125899906842624 |};
                      Float.runtime := {| Float.ieee := SpecFloat.S754_finite false 5629499534213120 (-50);
                                        Float.canonical_value := const_runtime_canonical F64 {| Float.numerator := 5; Float.denominator := 1; Float.canonical := gcd_z_1 5 |} |};
                      Float.coherent := eq_refl;
                      Float.shape := const_runtime_shape F64 {| Float.numerator := 5; Float.denominator := 1; Float.canonical := gcd_z_1 5 |}
                                     {| Float.numerator := 5; Float.denominator := 1; Float.canonical := Float.reduce_well_formed 5629499534213120 1125899906842624 |} eq_refl |}) ;
            use_resolved :=
              Some (PackResolved (Typing.FloatType F64)
                      (Typing.TypedFloat F64
                         {| Float.exact := {| Float.numerator := 5; Float.denominator := 1; Float.canonical := Float.reduce_well_formed 5629499534213120 1125899906842624 |};
                            Float.runtime := {| Float.ieee := SpecFloat.S754_finite false 5629499534213120 (-50);
                                              Float.canonical_value := const_runtime_canonical F64 {| Float.numerator := 5; Float.denominator := 1; Float.canonical := gcd_z_1 5 |} |};
                            Float.coherent := eq_refl;
                            Float.shape := const_runtime_shape F64 {| Float.numerator := 5; Float.denominator := 1; Float.canonical := gcd_z_1 5 |}
                                           {| Float.numerator := 5; Float.denominator := 1; Float.canonical := Float.reduce_well_formed 5629499534213120 1125899906842624 |} eq_refl |})) |}.
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** repeated equal literals are not deduplicated, because the table is keyed by occurrence identity *)
Definition dup_lit_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1; Syntax.IntegerLiteral 1 ] ] ].
Example dup_lit_ok : source_spec_valid_b dup_lit_program = true. Proof. vm_compute. reflexivity. Qed.

(* two entries at distinct keys with equal values: same syntax, two occurrences, two entries *)
Theorem dup_lit_facts_exact :
  Index.KeyMap.elements (program_expr_facts dup_lit_program)
  = [ (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive,
        MakeExpressionFact (Typing.UntypedInfo (Typing.IntegerConstant 1)) (Some (PackResolved (Typing.IntegerType Integer.Int) (Typing.TypedInteger Integer.Int 1 eq_refl))))
    ; (Index.MakeKey (FilePath.Make "main.go" eq_refl) 6%positive,
        MakeExpressionFact (Typing.UntypedInfo (Typing.IntegerConstant 1)) (Some (PackResolved (Typing.IntegerType Integer.Int) (Typing.TypedInteger Integer.Int 1 eq_refl)))) ].
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** only the outer argument resolves in a use context, and it resolves once from its own status *)
Definition nested_use_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)) ] ] ].
Example nested_use_ok : source_spec_valid_b nested_use_program = true. Proof. vm_compute. reflexivity. Qed.
Theorem nested_use_single_resolution :
  map (fun kv => (Index.key_local (fst kv),
                  match const_status (snd kv) with Typing.UntypedInfo _ => None | Typing.TypedInfo t _ => Some t end,
                  match use_resolved (snd kv) with Some _ => true | None => false end))
      (Index.KeyMap.elements (program_expr_facts nested_use_program))
  = [ (5%positive, Some (Typing.IntegerType Integer.Int16), true)    (* the println ARGUMENT — resolves ONCE *)
    ; (7%positive, Some (Typing.IntegerType Integer.Int8),  false)   (* the inner conversion OPERAND — no use-resolution *)
    ; (9%positive, None,                   false)   (* the literal 5 — untyped operand *)
    ].
Proof. rewrite program_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** an inner conversion that overflows gives one diagnostic at that conversion, and none outside it *)
Definition inner_fail_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)) ] ] ].
Theorem inner_fail_one_inner_no_outer :
  erased_report inner_fail_program (Index.Snapshot.index_program inner_fail_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 7%positive))
        [ AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive) ]
        (Some (Typing.IntegerType Integer.Int8)) None (Some (Syntax.type_expr_of_name Names.Int8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* the deep-nested phase fixtures: a valid four-deep chain reports nothing, an inner failure reports once *)
Definition deep_nested_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
                          (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                            (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
                              (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))) ] ] ].
Example deep_nested_valid : source_spec_valid_b deep_nested_program = true.
Proof. vm_compute. reflexivity. Qed.
Lemma deep_nested_compiles : Admissible deep_nested_program.
Proof.
  split.
  - unfold fresh_build_preflight_ok. vm_compute. reflexivity.
  - exact (proj1 (source_spec_valid_b_iff deep_nested_program) deep_nested_valid).
Qed.
(* a specification fixture over the erased report, not over the retained phase *)
Theorem deep_nested_no_diags :
  erased_report deep_nested_program (Index.Snapshot.index_program deep_nested_program) = [].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

Definition deep_fail_program : Syntax.Program :=
  singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
    [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
                          (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                            (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
                              (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)))) ] ] ].
(* one erased diagnostic at the innermost overflow; the enclosing conversions are blocked by their child *)
Theorem deep_fail_one_diag :
  length (erased_report deep_fail_program (Index.Snapshot.index_program deep_fail_program)) = 1%nat.
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** the real phase fixtures query the retained phase's own diagnostic projection *)
Theorem deep_nested_phase_no_diags (input : Input deep_nested_program) (ph : Phase input) :
  phase_diags (ph) = [].
Proof.
  rewrite phase_diags_eq_expr_diags.
  apply (proj2 (expression_diags_empty_iff
                  (index (input)))).
  vm_compute. reflexivity.
Qed.

(* the built phase reports the inner failure rather than suppressing it *)
Theorem deep_fail_phase_reports (input : Input deep_fail_program) (ph : Phase input) :
  phase_diags (ph) <> [].
Proof.
  rewrite phase_diags_eq_expr_diags. intro Hnil.
  pose proof (proj1 (expression_diags_empty_iff
                  (index (input))) Hnil) as Htyped.
  vm_compute in Htyped. discriminate Htyped.
Qed.

(* on a real compiled program the index mints a real reference, its hypotheses discharged from source *)
Lemma valid_localb_of_source (f : Syntax.File) (local : positive) occ :
  Index.source_occurrence_at f local = Some occ -> Index.valid_localb f local = true.
Proof. intro H. unfold Index.valid_localb. rewrite Index.build_file_source_exact, H. reflexivity. Qed.

Lemma program_expr_ref_at (p : Syntax.Program) (path : FilePath.T) (f : Syntax.File) (local : positive) occ e :
  find_file path (Syntax.files p) = Some f ->
  Index.source_occurrence_at f local = Some occ ->
  Index.view_expr occ = Some e ->
  exists (r : Index.Snapshot.NodeRef p) (er : Index.ExprRef p),
    In (r, occ) (program_visit p)
    /\ Index.as_expr (Index.indexed_syntax (Index.index_program p)) r = Some er
    /\ Index.Snapshot.node_ref_key r = Index.MakeKey path local.
Proof.
  intros Hfind Hsrc Hview.
  destruct (Index.Snapshot.ref_of_key_source p (Index.indexed_syntax (Index.index_program p))
              path f local Hfind (valid_localb_of_source f local occ Hsrc)) as [r [Hrok [Hrlocal Hrsource]]].
  pose proof (Index.Snapshot.source_occ_of_ref_eq r) as Hso.
  rewrite Hrlocal, Hrsource, Hsrc in Hso. injection Hso as Hoccr.
  assert (Hk : Index.Snapshot.node_kind (Index.indexed_syntax (Index.index_program p)) r = Index.ExpressionKind).
  { rewrite (Index.Snapshot.node_kind_matches_source p _ r), <- Hoccr. exact (Index.view_expr_kind occ e Hview). }
  destruct (Index.as_kind_complete (Index.indexed_syntax (Index.index_program p)) r Index.ExpressionKind Hk)
    as [er [Hae Her]].
  exists r, er. split; [ | split ].
  - rewrite Hoccr. apply noderef_in_prog_visit.
  - exact Hae.
  - exact (Index.Snapshot.ref_of_key_sound p (Index.indexed_syntax (Index.index_program p))
             (Index.MakeKey path local) r Hrok).
Qed.

(* a real conversion's target reference, minted at the target child key and recovering its source syntax *)
Lemma program_conv_target_ref (p : Syntax.Program) (path : FilePath.T) (f : Syntax.File) (local : positive) occ ts x :
  find_file path (Syntax.files p) = Some f ->
  Index.source_occurrence_at f local = Some occ ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  exists (er : Index.ExprRef p) tr,
    conversion_target_ref (Index.indexed_syntax (Index.index_program p)) er = Some tr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr) = Index.MakeKey path (Pos.succ local)
    /\ Index.type_name_ref_syntax tr = Some ts.
Proof.
  intros Hfind Hsrc Hview.
  destruct (program_expr_ref_at p path f local occ (Syntax.Convert ts x) Hfind Hsrc Hview)
    as [r [er [Hin [Hae Hkey]]]].
  destruct (conversion_target_ref_conv (Index.indexed_syntax (Index.index_program p)) r occ er ts x Hin Hview Hae)
    as [tr [Hc [Hktr [_ Hsyn]]]].
  assert (Hlocal : Index.Snapshot.node_ref_local r = local).
  { pose proof Hkey as Hkey2. rewrite Index.Snapshot.node_ref_key_eq in Hkey2. injection Hkey2 as _ Hl. exact Hl. }
  exists er, tr. split; [ exact Hc | split; [ | exact Hsyn ] ].
  rewrite Hktr. unfold type_name_key. rewrite Hkey. cbn [Index.key_path]. rewrite Hlocal. reflexivity.
Qed.

(** a real source occurrence yields a real retained work item, so a fixture can query the production table *)
Lemma member_at_in_forest (p : Syntax.Program) (input : Input p) (forest : WorkForest input)
    (path : FilePath.T) (f : Syntax.File) (local : positive) occ e :
  find_file path (Syntax.files p) = Some f ->
  Index.source_occurrence_at f local = Some occ ->
  Index.view_expr occ = Some e ->
  exists (wm : WorkMember forest),
    work_occurrence (proj1_sig wm) = occ /\ work_expr (proj1_sig wm) = e
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm)) = Index.MakeKey path local.
Proof.
  intros Hfind Hsrc Hview.
  destruct (program_expr_ref_at p path f local occ e Hfind Hsrc Hview) as [r [er [Hin [Hae Hkey]]]].
  assert (Hin' : In (r, occ) (input_visit input)) by (rewrite (input_visit_ok input); exact Hin).
  destruct (forest_forward forest r occ e Hin' Hview) as [w' [Hinw' [Hnr' Hocc']]].
  exists (exist _ w' Hinw'). cbn [proj1_sig]. split; [exact Hocc' | split].
  - pose proof (work_view_exact w') as Hv2. rewrite Hocc', Hview in Hv2. injection Hv2 as Hx. exact (eq_sym Hx).
  - rewrite Hnr'; exact Hkey.
Qed.

(** a real compiled program with two conversions to one source name at distinct arguments *)
Definition two_uint8_src : Syntax.File :=
  main_source [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 0)
                                 ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 1) ] ] ].
Definition two_uint8_program : Syntax.Program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
  [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 0)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 1) ] ] ].
Example two_uint8_ok : source_spec_valid_b two_uint8_program = true. Proof. vm_compute. reflexivity. Qed.

(* one uint8 conversion's real target ref (its source occurrence discharged by [vm_compute] in the caller). *)
Lemma two_uint8_conv_ref (local : positive) (n : N) occ :
  Index.source_occurrence_at two_uint8_src local = Some occ ->
  Index.view_expr occ = Some (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral n)) ->
  exists (er : Index.ExprRef two_uint8_program) tr,
    conversion_target_ref (Index.indexed_syntax (Index.index_program two_uint8_program)) er = Some tr
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr) = Index.MakeKey (FilePath.Make "main.go" eq_refl) (Pos.succ local)
    /\ Index.type_name_ref_syntax tr = Some (Syntax.type_expr_of_name Names.Uint8).
Proof.
  intros Hsrc Hview.
  exact (program_conv_target_ref two_uint8_program (FilePath.Make "main.go" eq_refl) two_uint8_src local occ
           (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral n) ltac:(vm_compute; reflexivity) Hsrc Hview).
Qed.

(* the two-name program compiles, so elaboration exposes a real retained result *)
Lemma two_uint8_compiles : Admissible two_uint8_program.
Proof.
  split.
  - unfold fresh_build_preflight_ok. vm_compute. reflexivity.
  - exact (proj1 (source_spec_valid_b_iff two_uint8_program) two_uint8_ok).
Qed.

Theorem two_uint8_distinct_target_refs :
  exists (Hnil : core_diagnostics (elaboration_core (elaborate two_uint8_program)) = nil)
         facts (er1 er2 : Index.ExprRef two_uint8_program) tr1 tr2,
    (* the facts come from an actual successful elaboration, projected from its retained core *)
    facts = core_facts (elaboration_core (elaborate two_uint8_program)) Hnil
    /\ conversion_target_ref (Index.indexed_syntax (Index.index_program two_uint8_program)) er1 = Some tr1
    /\ conversion_target_ref (Index.indexed_syntax (Index.index_program two_uint8_program)) er2 = Some tr2
    /\ Index.Snapshot.node_ref_key (Index.erase_ref tr1) <> Index.Snapshot.node_ref_key (Index.erase_ref tr2)
    /\ Index.type_name_ref_syntax tr1 = Index.type_name_ref_syntax tr2
    (* distinct occurrence references, equal recovered syntax, equal sealed facts *)
    /\ type_name_fact_at facts tr1 = type_name_fact_at facts tr2.
Proof.
  pose proof (proj2 (elaboration_accepted_iff_admissible two_uint8_program) two_uint8_compiles) as Hnil.
  pose (facts := core_facts (elaboration_core (elaborate two_uint8_program)) Hnil).
  destruct (Index.source_occurrence_at two_uint8_src 5) as [occ1|] eqn:Eo1; [| vm_compute in Eo1; discriminate Eo1].
  destruct (Index.source_occurrence_at two_uint8_src 8) as [occ2|] eqn:Eo2; [| vm_compute in Eo2; discriminate Eo2].
  destruct (two_uint8_conv_ref 5 0 occ1 Eo1
              ltac:(vm_compute in Eo1; injection Eo1 as <-; vm_compute; reflexivity)) as [er1 [tr1 [Hc1 [Hk1 Hs1]]]].
  destruct (two_uint8_conv_ref 8 1 occ2 Eo2
              ltac:(vm_compute in Eo2; injection Eo2 as <-; vm_compute; reflexivity)) as [er2 [tr2 [Hc2 [Hk2 Hs2]]]].
  exists Hnil, facts, er1, er2, tr1, tr2.
  split; [ reflexivity | split; [ exact Hc1 | split; [ exact Hc2 | split; [ | split ] ] ] ].
  - rewrite Hk1, Hk2. intro Hbad. apply (f_equal Index.key_local) in Hbad. vm_compute in Hbad. discriminate Hbad.
  - rewrite Hs1, Hs2. reflexivity.
  - rewrite (type_name_fact_at_resolves facts tr1 _ Hs1),
            (type_name_fact_at_resolves facts tr2 _ Hs2). reflexivity.
Qed.

(** the direct production queries build a real work item and read the phase's own outcome table *)
Lemma filter_map_length {A B} (q : B -> bool) (g : A -> B) (l : list A) :
  length (filter q (map g l)) = length (filter (fun x => q (g x)) l).
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [map filter].
  destruct (q (g a)); cbn [length]; rewrite IH; reflexivity.
Qed.

Definition deep_nested_src : Syntax.File := main_source
  [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
                        (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                          (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
                            (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))) ] ] ].
Definition deep_fail_src : Syntax.File := main_source
  [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
                        (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                          (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
                            (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)))) ] ] ].

(* a conversion whose own step does not fail but whose fact is absent is a child failure *)
Definition childfail_conversion_at (input : Input deep_fail_program) (ph : Phase input)
    (local : positive) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Prop :=
  exists occ (wm : WorkMember (phase_work ph)),
       Index.source_occurrence_at deep_fail_src local = Some occ
    /\ Index.view_expr occ = Some (Syntax.Convert ts x)
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) local
    /\ childfail_conversion_cause (phase_ot ph) wm ts x.

Lemma deep_fail_childfail_at (input : Input deep_fail_program) (ph : Phase input) (local : positive) ts x occ :
  Index.source_occurrence_at deep_fail_src local = Some occ ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  occurrence_expr_fact occ = None ->
  local_conv_failure (Syntax.Convert ts x) = None ->
  childfail_conversion_at input ph local ts x.
Proof.
  intros Hsrc Hview Hnf Hlcf.
  destruct (member_at_in_forest deep_fail_program input (phase_work ph) (FilePath.Make "main.go" eq_refl) deep_fail_src local occ (Syntax.Convert ts x)
              ltac:(vm_compute; reflexivity) Hsrc Hview) as [wm [Hocc [He Hkey]]].
  exists occ, wm.
  split; [ exact Hsrc | split; [ exact Hview | split; [ exact Hocc | split; [ exact Hkey | ] ] ] ].
  apply (retained_childfail_cause (phase_ot ph) wm ts x He).
  apply (total_forest_outcome_childfail_shape _ wm ts x);
    [ rewrite Hocc; exact Hview | rewrite Hocc; exact Hnf | exact Hlcf ].
Qed.

(* an occurrence whose fact succeeds is a success on the production table *)
Lemma deep_nested_ok_at (input : Input deep_nested_program) (ph : Phase input) (local : positive) e occ :
  Index.source_occurrence_at deep_nested_src local = Some occ ->
  Index.view_expr occ = Some e ->
  (exists f, occurrence_expr_fact occ = Some f) ->
  (* the member is returned with its occurrence identity, which is what keeps the fixture from weakening *)
  exists (wm : WorkMember (phase_work (ph))) f,
    work_expr (proj1_sig wm) = e
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) local
    /\ total_forest_outcome_at
         (phase_ot (ph)) wm
       = ExpressionSuccess f.
Proof.
  intros Hsrc Hview [f Hf].
  destruct (member_at_in_forest deep_nested_program input (phase_work ph) (FilePath.Make "main.go" eq_refl) deep_nested_src local occ e
              ltac:(vm_compute; reflexivity) Hsrc Hview) as [wm [Hocc [He Hkey]]].
  exists wm, f. split; [exact He | split; [ exact Hocc | split; [ exact Hkey | ] ] ].
  apply (total_forest_outcome_ok_of_fact _ wm f). rewrite Hocc. exact Hf.
Qed.

(* the innermost overflow is the sole failure, its direct cause reading the operand's stored success *)
Theorem deep_fail_innermost_convfail (input : Input deep_fail_program) (ph : Phase input) :
  let ot := phase_ot (ph) in
  exists occ (wm : WorkMember (phase_work (ph)))
         (rest : list (Work input))
         (acc_rest : Accumulator (phase_work (ph))
                       (phase_type_name_facts (ph)) rest)
         (step : ConversionStep (phase_work (ph)) (proj1_sig wm) rest
                   (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)) opf t,
       (* the failing member is the one at SOURCE LOCAL 11 — not merely some member of that shape *)
       Index.source_occurrence_at deep_fail_src 11 = Some occ
    /\ Index.view_expr occ = Some (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) 11
    /\ work_expr (proj1_sig wm) = Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)
    /\ total_forest_outcome_at ot wm
         = ConversionFailure (work_expr_ref (proj1_sig wm)) (conversion_target_node_ref (step_conversion step))
             (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step)))) t (const_status opf)
    (* the operand outcome read THROUGH the exact operand SuffixMember of the RETAINED tail accumulator *)
    /\ accumulator_total acc_rest (step_operand_suffix step) = ExpressionSuccess opf
    (* the same operand member carries that same success in the final table, through the trace's preservation *)
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step)) = ExpressionSuccess opf
    /\ total_forest_outcome_at ot (proj1_sig (step_operand_suffix step))
         = accumulator_total acc_rest (step_operand_suffix step)
    /\ Typing.convert_constant t (const_status opf) = None
    (* the resolved target type of the failing conversion IS the exact predeclared-context Index.table query *)
    /\ t = fact_type (type_name_fact_at_table (phase_type_name_facts (ph))
                       (conversion_target_node_ref (step_conversion step))).
Proof.
  cbn zeta.
  destruct (Index.source_occurrence_at deep_fail_src 11) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
  destruct (member_at_in_forest deep_fail_program input (phase_work ph) (FilePath.Make "main.go" eq_refl) deep_fail_src 11 occ
              (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)) ltac:(vm_compute; reflexivity) Eo
              ltac:(vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity)) as [wm [Hocc [He Hkey]]].
  destruct (total_forest_outcome_convfail_shape
              (phase_ot (ph))
              wm (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))
    as [er2 [tr2 [opr2 [t [ci Hout]]]]].
  { rewrite Hocc. vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity. }
  { rewrite Hocc. vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity. }
  { vm_compute; discriminate. }
  (* project the retained cause off the trace, with its tail split and its preservation *)
  destruct (total_forest_outcome_cause
              (phase_ot (ph))
              wm) as [rest [acc_rest [[Hsplit stepc] Hpreserve]]].
  (* the total query is definitionally the accumulator query, so the cause's index rewrites directly *)
  assert (Hidx : accumulator_total (outcomes_acc (phase_ot (ph)))
                   (wm_suffix wm) = ConversionFailure er2 tr2 opr2 t ci) by exact Hout.
  rewrite Hidx in stepc.
  destruct (conversion_failure_cause_yields_step _ rest acc_rest er2 tr2 opr2 t ci stepc)
    as [ts0 [x0 [step [opf [Hstep_e [Hopf [Her2 [Htr2 [Hopr2 [Ht [Hci Hcv]]]]]]]]]]].
  assert (Heq : Syntax.Convert ts0 x0 = Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))
    by (rewrite <- Hstep_e; exact He).
  injection Heq as Hts0 Hx0. subst ts0 x0.
  (* the final-to-tail closure at the operand member: its FINAL-Index.table query = its retained tail query *)
  pose proof (final_operand_outcome
                (phase_ot (ph))
                rest acc_rest Hpreserve (step_operand_suffix step)) as Hclose.
  exists occ, wm, rest, acc_rest, step, opf, t.
  (* the conjunct closes by reflexivity here, but the statement still carries it, which is the point *)
  split; [ reflexivity | ].
  split; [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity | ].
  split; [ exact Hocc | split; [ exact Hkey | ] ].
  split; [ exact He | split; [ | split; [ exact Hopf | split; [ | split; [ | split ] ] ] ] ].
  - rewrite Hout, Her2, Htr2, Hopr2, Hci. reflexivity.
  - transitivity (accumulator_total acc_rest (step_operand_suffix step)); [ exact Hclose | exact Hopf ].
  - exact Hclose.
  - rewrite <- Hci. exact Hcv.
  - exact Ht.
Qed.

(* the three enclosing conversions are each a child failure, queried at their exact work items *)
Definition deep_fail_outer_childfail_claim (input : Input deep_fail_program) (ph : Phase input) : Prop :=
  let ot := phase_ot (ph) in
  childfail_conversion_at input ph 9 (Syntax.type_expr_of_name Names.Int16)
       (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))
  /\ childfail_conversion_at input ph 7 (Syntax.type_expr_of_name Names.Int32)
       (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)))
  /\ childfail_conversion_at input ph 5 (Syntax.type_expr_of_name Names.Int64)
       (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
         (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)))).

Theorem deep_fail_outer_childfail (input : Input deep_fail_program) (ph : Phase input) :
  deep_fail_outer_childfail_claim input ph.
Proof.
  unfold deep_fail_outer_childfail_claim.
  cbn zeta.
  split; [ | split ].
  - destruct (Index.source_occurrence_at deep_fail_src 9) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_fail_childfail_at input ph 9 (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_fail_src 7) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_fail_childfail_at input ph 7 (Syntax.type_expr_of_name Names.Int32)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_fail_src 5) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_fail_childfail_at input ph 5 (Syntax.type_expr_of_name Names.Int64)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
               (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute; reflexivity ].
Qed.

(* §12.2 — the STORED diagnostic list of the deep_fail phase is EXACTLY ONE reason (not merely nonempty). *)
Theorem deep_fail_exactly_one_diag (input : Input deep_fail_program) (ph : Phase input) :
  length (phase_diags (ph)) = 1%nat.
Proof.
  (* the visit carries opaque proofs, so the count bridges to the source-computable erased report *)
  rewrite phase_diags_eq_expr_diags.
  set (idx0 := index (input)).
  assert (Hpkg : package_diags idx0 = []) by (apply (proj2 (package_diags_empty_iff idx0)); vm_compute; reflexivity).
  assert (Hexpr : expression_diags idx0 ++ package_diags idx0 = expression_diags idx0) by (rewrite Hpkg; apply app_nil_r).
  pose proof (f_equal (@length _) (erased_src_diags_eq idx0)) as H.
  rewrite Hexpr, map_length in H. rewrite H. vm_compute. reflexivity.
Qed.

(* the innermost failure's retained cause is connected to the exact stored diagnostic *)
Definition deep_fail_innermost_diag_claim (c : Core deep_fail_program) : Prop :=
  exists occ (wm : WorkMember (phase_work (phase c))),
       (* the failing member is the one at SOURCE LOCAL 11 *)
       Index.source_occurrence_at deep_fail_src 11 = Some occ
    /\ Index.view_expr occ = Some (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300))
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) 11
    /\ rejected_conversion_cause (phase_ot (phase c)) wm
      (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 300)
      (fun step opf t =>
         exists (wma : WorkMember (phase_work (phase c))) (outer : list (Index.ExprRef deep_fail_program)),
           (* the exact annotated member whose underlying work item is this failing conversion's *)
           In (wma, outer) (annotated_items (phase_awork (phase c)))
           /\ proj1_sig wma = proj1_sig wm
           /\ (let reason :=
                  InvalidConversion (work_expr_ref (proj1_sig wm))
                    (conversion_target_node_ref (step_conversion step))
                    (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                    outer t (const_status opf) in
                   phase_diags (phase c) = [reason]
                /\ core_raw_diagnostics c = [reason]
                /\ core_diagnostics c = [reason])).

Theorem deep_fail_innermost_diag (c : Core deep_fail_program) : deep_fail_innermost_diag_claim c.
Proof.
  unfold deep_fail_innermost_diag_claim.
  (* the member and its exact ConversionFailure, from the shape fixture over this core's OWN phase *)
  pose proof deep_fail_innermost_convfail (core_input c) (phase c) as H. cbn zeta in H.
  destruct H as [occ [wm [rest0 [acc0 [step0 [opf0 [t0 [Esrc [Hview [Hoccw [Hkey [He [Hout0 _]]]]]]]]]]]]].
  exists occ, wm.
  split; [ exact Esrc | split; [ exact Hview | split; [ exact Hoccw | split; [ exact Hkey | ] ] ] ].
  apply (retained_convfail_cause (phase_ot (phase c)) wm _ _ _ _ _ _ _ _ He Hout0).
  (* everything below is stated over the step the RETAINED CAUSE supplied, not over [step0] *)
  intros step opf He' Hout.
  destruct (retained_convfail_diag (phase_ot (phase c)) (phase_awork (phase c)) wm
              (work_expr_ref (proj1_sig wm)) (conversion_target_node_ref (step_conversion step))
              (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
              t0 (const_status opf) Hout)
    as [wma [outer [Hinm [Hwma Hin]]]].
  exists wma, outer.
  split; [ exact Hinm | split; [ exact Hwma | ] ]. cbv zeta.
  (* (1) the retained phase reports EXACTLY this reason *)
  assert (Hphase : phase_diags (phase c)
                   = [ InvalidConversion (work_expr_ref (proj1_sig wm))
                         (conversion_target_node_ref (step_conversion step))
                         (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                         outer t0 (const_status opf) ]).
  { assert (Hdiageq : phase_diags (phase c)
              = flat_map (forest_awork_diags (phase_ot (phase c)))
                  (annotated_items (phase_awork (phase c))))
      by (unfold phase_diags; exact (erased_is_diagnostics (phase_diag (phase c)))).
    apply length_one_in_eq.
    - exact (deep_fail_exactly_one_diag (core_input c) (phase c)).
    - rewrite Hdiageq. exact Hin. }
  split; [ exact Hphase | ].
  (* (2) the core's RAW list is the phase's own followed by its package map's, and that map is clean *)
  assert (Hpkg : package_diags (core_index c) = nil)
    by (apply (proj2 (package_diags_empty_iff (core_index c))); vm_compute; reflexivity).
  assert (Hraw : core_raw_diagnostics c
                 = [ InvalidConversion (work_expr_ref (proj1_sig wm))
                       (conversion_target_node_ref (step_conversion step))
                       (work_expr_ref (proj1_sig (conversion_operand_work (step_conversion step))))
                       outer t0 (const_status opf) ]).
  { rewrite (core_raw_diagnostics_exact c), (core_package_diags_canonical c), Hpkg, Hphase.
    exact (app_nil_r _). }
  split; [ exact Hraw | ].
  (* (3) …and the COMMAND-ORDERED list at that one node-anchored reason is the same singleton *)
  apply (core_diagnostics_of_node_singleton c _
           (Index.Snapshot.node_ref_key (Index.erase_ref (work_expr_ref (proj1_sig wm)))) Hraw).
  - reflexivity.
  - rewrite (core_plan_is_fresh_build_plan c). vm_compute. reflexivity.
Qed.

(* the shape-only projection, named for what it drops so nobody reaches for it where identity matters *)
Lemma deep_nested_ok_at_shape (input : Input deep_nested_program) (ph : Phase input) (local : positive) e occ :
  Index.source_occurrence_at deep_nested_src local = Some occ ->
  Index.view_expr occ = Some e ->
  (exists f, occurrence_expr_fact occ = Some f) ->
  exists (wm : WorkMember (phase_work (ph))) f,
    work_expr (proj1_sig wm) = e
    /\ total_forest_outcome_at (phase_ot (ph)) wm = ExpressionSuccess f.
Proof.
  intros Hsrc Hview Hfact.
  destruct (deep_nested_ok_at input ph local e occ Hsrc Hview Hfact) as [wm [f [He [_ [_ Hok]]]]].
  exists wm, f. split; [ exact He | exact Hok ].
Qed.

(* every conversion of the valid chain and its leaf resolve successfully, with no fail-open anywhere *)
Theorem deep_nested_all_ok (input : Input deep_nested_program) (ph : Phase input) :
  let ot := phase_ot (ph) in
  (exists (wm : WorkMember (phase_work (ph))) f,
     work_expr (proj1_sig wm) = Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
                   (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                     (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))))
     /\ total_forest_outcome_at ot wm = ExpressionSuccess f)
  /\ (exists (wm : WorkMember (phase_work (ph))) f,
        work_expr (proj1_sig wm) = Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
                      (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))
        /\ total_forest_outcome_at ot wm = ExpressionSuccess f)
  /\ (exists (wm : WorkMember (phase_work (ph))) f,
        work_expr (proj1_sig wm) = Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))
        /\ total_forest_outcome_at ot wm = ExpressionSuccess f)
  /\ (exists (wm : WorkMember (phase_work (ph))) f,
        work_expr (proj1_sig wm) = Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)
        /\ total_forest_outcome_at ot wm = ExpressionSuccess f)
  /\ (exists (wm : WorkMember (phase_work (ph))) f,
        work_expr (proj1_sig wm) = Syntax.IntegerLiteral 5 /\ total_forest_outcome_at ot wm = ExpressionSuccess f).
Proof.
  cbn zeta.
  split; [ | split; [ | split; [ | split ] ] ].
  - destruct (Index.source_occurrence_at deep_nested_src 5) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_ok_at_shape input ph 5 (Syntax.Convert (Syntax.type_expr_of_name Names.Int64)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
               (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 7) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_ok_at_shape input ph 7 (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 9) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_ok_at_shape input ph 9 (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 11) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_ok_at_shape input ph 11 (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 13) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_ok_at_shape input ph 13 (Syntax.IntegerLiteral 5) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
Qed.

(** the per-occurrence success evidence, which a syntactically equal conversion elsewhere cannot satisfy *)
Definition accepted_conversion_at (input : Input deep_nested_program) (ph : Phase input)
    (local : positive) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Prop :=
  exists occ (wm : WorkMember (phase_work ph)),
       Index.source_occurrence_at deep_nested_src local = Some occ
    /\ Index.view_expr occ = Some (Syntax.Convert ts x)
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) local
    /\ accepted_conversion_cause (phase_ot ph) wm ts x.

(* any valid occurrence instantiates the cause-owned evidence on the phase's own table *)
Lemma deep_nested_convsuccess_at (input : Input deep_nested_program) (ph : Phase input) (local : positive) ts x occ :
  Index.source_occurrence_at deep_nested_src local = Some occ ->
  Index.view_expr occ = Some (Syntax.Convert ts x) ->
  (exists f, occurrence_expr_fact occ = Some f) ->
  accepted_conversion_at input ph local ts x.
Proof.
  intros Hsrc Hview Hfact.
  destruct (deep_nested_ok_at input ph local (Syntax.Convert ts x) occ Hsrc Hview Hfact)
    as [wm [f [He [Hocc [Hkey Hok]]]]].
  exists occ, wm.
  split; [ exact Hsrc | split; [ exact Hview | split; [ exact Hocc | split; [ exact Hkey | ] ] ] ].
  exact (retained_convsuccess_cause (phase_ot ph) wm ts x f He Hok).
Qed.

(* all four valid-chain conversions carry the cause-owned evidence, each keeping its own exact step *)
Theorem deep_nested_chain_success_evidence (input : Input deep_nested_program) (ph : Phase input) :
  accepted_conversion_at input ph 11 (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)
  /\ accepted_conversion_at input ph 9 (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))
  /\ accepted_conversion_at input ph 7 (Syntax.type_expr_of_name Names.Int32)
       (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))
  /\ accepted_conversion_at input ph 5 (Syntax.type_expr_of_name Names.Int64)
       (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))).
Proof.
  split; [ | split; [ | split ] ].
  - destruct (Index.source_occurrence_at deep_nested_src 11) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_convsuccess_at input ph 11 (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 9) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_convsuccess_at input ph 9 (Syntax.type_expr_of_name Names.Int16)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 7) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_convsuccess_at input ph 7 (Syntax.type_expr_of_name Names.Int32)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
  - destruct (Index.source_occurrence_at deep_nested_src 5) as [occ|] eqn:Eo; [| vm_compute in Eo; discriminate Eo].
    apply (deep_nested_convsuccess_at input ph 5 (Syntax.type_expr_of_name Names.Int64)
             (Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))) occ Eo);
      [ vm_compute in Eo; injection Eo as <-; vm_compute; reflexivity
      | vm_compute in Eo; injection Eo as <-; eexists; vm_compute; reflexivity ].
Qed.

(* the direct work-index fixtures: each conversion's carried reference finds the exact retained operand *)
Definition twin_expr_src : Syntax.File :=
  main_source [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
                                 ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7) ] ] ].
Definition twin_expr_program : Syntax.Program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl)
  [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7) ] ] ].
Example twin_expr_ok : source_spec_valid_b twin_expr_program = true. Proof. vm_compute. reflexivity. Qed.

(* equal value, distinct occurrence, over any retained forest rather than only the built one *)
Theorem twin_distinct_in_forest (input : Input twin_expr_program) (forest : WorkForest input) :
  exists w1 w2 : Work input,
       In w1 (forest_items forest) /\ In w2 (forest_items forest)
       (* the SAME source expression value at two occurrences *)
    /\ work_expr w1 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
    /\ work_expr w2 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
       (* yet DISTINCT occurrence keys, DISTINCT index entries, and DISTINCT work items *)
    /\ Index.Snapshot.node_ref_key (work_node_ref w1) <> Index.Snapshot.node_ref_key (work_node_ref w2)
    /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w1))
         (index_map (forest_index forest)) = Some w1
    /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w2))
         (index_map (forest_index forest)) = Some w2
    /\ w1 <> w2.
Proof.
  destruct (Index.source_occurrence_at twin_expr_src 5) as [occ1|] eqn:Eo1;
    [| vm_compute in Eo1; discriminate Eo1].
  destruct (Index.source_occurrence_at twin_expr_src 8) as [occ2|] eqn:Eo2;
    [| vm_compute in Eo2; discriminate Eo2].
  destruct (member_at_in_forest twin_expr_program input forest (FilePath.Make "main.go" eq_refl) twin_expr_src 5 occ1
              (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7))
              ltac:(vm_compute; reflexivity) Eo1
              ltac:(vm_compute in Eo1; injection Eo1 as <-; vm_compute; reflexivity))
    as [wm1 [Hocc1 [He1 Hk1]]].
  destruct (member_at_in_forest twin_expr_program input forest (FilePath.Make "main.go" eq_refl) twin_expr_src 8 occ2
              (Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7))
              ltac:(vm_compute; reflexivity) Eo2
              ltac:(vm_compute in Eo2; injection Eo2 as <-; vm_compute; reflexivity))
    as [wm2 [Hocc2 [He2 Hk2]]].
  assert (Hkne : Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm1))
                 <> Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm2))).
  { rewrite Hk1, Hk2. intro H.
    pose proof (f_equal Index.key_local H) as Hl. cbn [Index.key_local] in Hl. discriminate Hl. }
  exists (proj1_sig wm1), (proj1_sig wm2).
  split; [exact (proj2_sig wm1) | split; [exact (proj2_sig wm2) | split; [exact He1 | split; [exact He2 |]]]].
  split; [exact Hkne |].
  split.
  { exact (proj2 (index_exact (forest_index forest)
                    _ (proj1_sig wm1)) (conj (proj2_sig wm1) eq_refl)). }
  split.
  { exact (proj2 (index_exact (forest_index forest)
                    _ (proj1_sig wm2)) (conj (proj2_sig wm2) eq_refl)). }
  intro H. apply Hkne. rewrite H. reflexivity.
Qed.

(* any work forest over any input has as many members as the program has expression occurrences *)
Theorem forest_count_source {p} (input : Input p) (forest : WorkForest input) :
  length (forest_items forest)
  = length (filter (fun ko : Index.Key * Index.Occurrence =>
              match Index.view_expr (snd ko) with Some _ => true | None => false end)
            (keyed_visit p)).
Proof.
  rewrite <- (map_length (fun w => (work_node_ref w, work_occurrence w)) (forest_items forest)).
  rewrite (forest_items_exact forest), (input_visit_ok input).
  unfold keyed_visit. rewrite filter_map_length. reflexivity.
Qed.

(* …and therefore of the work forest a retained [Core] holds. *)
Theorem core_work_count_source {p} (core : Core p) :
  length (forest_items (phase_work (phase core)))
  = length (filter (fun ko : Index.Key * Index.Occurrence =>
              match Index.view_expr (snd ko) with Some _ => true | None => false end)
            (keyed_visit p)).
Proof. exact (forest_count_source (core_input core) (phase_work (phase core))). Qed.

(** the accepted root fixture mints nothing: every field is a query of the returned capability *)
Definition accepted_deep_core (cp : Program) (Hcp : source cp = deep_nested_program) : Core deep_nested_program :=
  eq_rect (source cp) Core (core cp) deep_nested_program Hcp.

Record AcceptedFixture (cp : Program) (Hcp : source cp = deep_nested_program) : Prop := MakeAcceptedFixture {
  (* ── one chain: the capability's input and phase ARE the retained core's, not copies beside it ── *)
  accepted_fixture_input : program_input cp = core_input (core cp) ;
  accepted_fixture_phase : program_phase cp = phase (core cp) ;

  (* ── the sealed fact tables ARE the retained phase's own objects, never rebuilt maps ── *)
  accepted_fixture_expression_facts :
    expression_facts (facts cp) = expression_facts_table (phase_fact_table (program_phase cp)) ;
  accepted_fixture_type_name_facts :
    type_name_facts (facts cp) = phase_type_name_facts (program_phase cp) ;

  (* ── buckets: the core's own, folded from the core's OWN retained visit ── *)
  accepted_fixture_package_refs : facts_package_refs (facts cp) = core_package_refs (core cp) ;
  accepted_fixture_package_refs_own_visit :
    core_package_refs (core cp)
    = program_package_refs_from_visit (index (core_input (core cp))) (input_visit (core_input (core cp))) ;

  (* ── layout and plan: the values the accepted decision used, and the program's canonical ones ── *)
  accepted_fixture_layout : program_root_layout cp = root_layout (source cp) ;
  accepted_fixture_plan : program_build_plan cp = fresh_build_plan (source cp) ;

  (* ── the retained work forest, and its size as a SOURCE quantity ── *)
  accepted_fixture_forest : length (forest_items (phase_work (phase (core cp)))) = 5%nat ;

  (* the retained index, exact in both directions over every member and key, as a whole-object law *)
  accepted_fixture_index_exact :
    forall k w,
      Index.KeyMap.find k (index_map (forest_index (phase_work (phase (core cp))))) = Some w
      <-> (In w (forest_items (phase_work (phase (core cp))))
           /\ Index.Snapshot.node_ref_key (work_node_ref w) = k) ;

  (* ── the retained outcome domain is EXACTLY the retained forest — again over the complete forest ── *)
  accepted_fixture_outcomes :
    forall k,
      Index.KeyMap.find k (outcomes_map (phase_ot (phase (core cp)))) <> None
      <-> exists w, In w (forest_items (phase_work (phase (core cp))))
                 /\ Index.Snapshot.node_ref_key (work_node_ref w) = k ;

  (* the retained trace explains every member's position, each cause carrying its own suffix split *)
  accepted_fixture_trace :
    forall wm : WorkMember (phase_work (phase (core cp))),
      exists prefix,
        forest_items (phase_work (phase (core cp)))
        = prefix ++ proj1_sig wm
                    :: projT1 (total_forest_outcome_cause (phase_ot (phase (core cp))) wm) ;

  (* the retained members sit at pairwise distinct keys, so no two occurrences share an entry *)
  accepted_fixture_distinct_occurrences :
    NoDup (map (fun w => Index.Snapshot.node_ref_key (work_node_ref w))
               (forest_items (phase_work (phase (core cp))))) ;

  (* the four conversion causes, each the exact object projected from that retained trace *)
  accepted_fixture_int8_cause :
    accepted_conversion_at (core_input (accepted_deep_core cp Hcp)) (phase (accepted_deep_core cp Hcp))
      11 (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5) ;
  accepted_fixture_int16_cause :
    accepted_conversion_at (core_input (accepted_deep_core cp Hcp)) (phase (accepted_deep_core cp Hcp))
      9 (Syntax.type_expr_of_name Names.Int16)
      (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)) ;
  accepted_fixture_int32_cause :
    accepted_conversion_at (core_input (accepted_deep_core cp Hcp)) (phase (accepted_deep_core cp Hcp))
      7 (Syntax.type_expr_of_name Names.Int32)
      (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
        (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5))) ;
  accepted_fixture_int64_cause :
    accepted_conversion_at (core_input (accepted_deep_core cp Hcp)) (phase (accepted_deep_core cp Hcp))
      5 (Syntax.type_expr_of_name Names.Int64)
      (Syntax.Convert (Syntax.type_expr_of_name Names.Int32)
        (Syntax.Convert (Syntax.type_expr_of_name Names.Int16)
          (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 5)))) ;

  (* acceptance is the retained diagnostic lists being empty, the phase's, the raw and the final *)
  accepted_fixture_phase_diagnostics : phase_diags (phase (core cp)) = nil ;
  accepted_fixture_raw_diagnostics : core_raw_diagnostics (core cp) = nil ;
  accepted_fixture_final_diagnostics : core_diagnostics (core cp) = nil
}.

(** the production compiler returns a capability, and that same witness satisfies the whole fixture *)
Theorem deep_nested_compile_fixture :
  exists cp Hcp,
    compile deep_nested_program = Compiled cp Hcp
    /\ AcceptedFixture cp Hcp.
Proof.
  destruct (compile_complete deep_nested_program deep_nested_compiles) as [cp [Hcp Hc]].
  exists cp, Hcp. split; [ exact Hc | ].
  constructor.
  - reflexivity.
  - reflexivity.
  - exact (compilable_retains_expr_facts cp).
  - reflexivity.
  - reflexivity.
  - exact (core_refs_fold_own_visit _ (core cp)).
  - exact (program_root_layout_retained cp).
  - exact (program_build_plan_retained cp).
  - rewrite (core_work_count_source (core cp)), Hcp, keyed_visit_source. vm_compute. reflexivity.
  - exact (index_exact (forest_index (phase_work (phase (core cp))))).
  - exact (outcomes_domain_iff_forest (phase_ot (phase (core cp)))).
  - intro wm.
    destruct (total_forest_outcome_cause (phase_ot (phase (core cp))) wm)
      as [rest [acc_rest [[Hsplit Hstep] Hpreserve]]].
    cbn [projT1]. exact Hsplit.
  - exact (forest_keys_nodup (phase_work (phase (core cp)))).
  - exact (proj1 (deep_nested_chain_success_evidence _ _)).
  - exact (proj1 (proj2 (deep_nested_chain_success_evidence _ _))).
  - exact (proj1 (proj2 (proj2 (deep_nested_chain_success_evidence _ _)))).
  - exact (proj2 (proj2 (proj2 (deep_nested_chain_success_evidence _ _)))).
  - exact (core_prop_at_source (fun q (c : Core q) => phase_diags (phase c) = nil) (core cp) Hcp
             (deep_nested_phase_no_diags _ _)).
  - refine (core_prop_at_source (fun q (c : Core q) => core_raw_diagnostics c = nil) (core cp) Hcp _).
    set (c := eq_rect (source cp) Core (core cp) deep_nested_program Hcp).
    rewrite (core_raw_diagnostics_exact c), (core_package_diags_canonical c),
            (deep_nested_phase_no_diags (core_input c) (phase c)); cbn [app].
    apply (proj2 (package_diags_empty_iff (core_index c))). vm_compute. reflexivity.
  - exact (accepted cp).
Qed.


Theorem twin_capability_retains_distinct_occurrences :
  exists cp Hcp,
    compile twin_expr_program = Compiled cp Hcp
    /\ exists w1 w2 : Work (core_input (core cp)),
         In w1 (forest_items (phase_work (phase (core cp))))
      /\ In w2 (forest_items (phase_work (phase (core cp))))
      /\ work_expr w1 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
      /\ work_expr w2 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
      /\ Index.Snapshot.node_ref_key (work_node_ref w1) <> Index.Snapshot.node_ref_key (work_node_ref w2)
      /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w1))
           (index_map (forest_index (phase_work (phase (core cp))))) = Some w1
      /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w2))
           (index_map (forest_index (phase_work (phase (core cp))))) = Some w2
      /\ w1 <> w2.
Proof.
  destruct (compile_complete twin_expr_program
              (admissible_of_source_spec_valid_b twin_expr_program twin_expr_ok
                 ltac:(vm_compute; reflexivity))) as [cp [Hcp Hc]].
  exists cp, Hcp. split; [ exact Hc | ].
  apply (core_prop_at_source
           (fun q (c : Core q) =>
              exists w1 w2 : Work (core_input c),
                In w1 (forest_items (phase_work (phase c)))
             /\ In w2 (forest_items (phase_work (phase c)))
             /\ work_expr w1 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
             /\ work_expr w2 = Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 7)
             /\ Index.Snapshot.node_ref_key (work_node_ref w1) <> Index.Snapshot.node_ref_key (work_node_ref w2)
             /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w1))
                  (index_map (forest_index (phase_work (phase c)))) = Some w1
             /\ Index.KeyMap.find (Index.Snapshot.node_ref_key (work_node_ref w2))
                  (index_map (forest_index (phase_work (phase c)))) = Some w2
             /\ w1 <> w2)
           (core cp) Hcp).
  exact (twin_distinct_in_forest _ _).
Qed.

(** the same discipline on the failing chain, where the failure is indexed so nothing transports *)
Record RejectedFixture (fail : Failure deep_fail_program) : Prop := MakeRejectedFixture {
  (* ── every failure query is a PROJECTION of the retained core, definitionally ── *)
  rejected_fixture_core : failure_diagnostics fail = core_diagnostics (failure_core fail) ;
  rejected_fixture_raw_diagnostics : failure_raw_diagnostics fail = core_raw_diagnostics (failure_core fail) ;
  rejected_fixture_input : failure_input fail = core_input (failure_core fail) ;
  rejected_fixture_phase : failure_phase fail = phase (failure_core fail) ;

  (* ── buckets: the core's own, folded from THAT failed elaboration's own retained visit ── *)
  rejected_fixture_package_refs : failure_package_refs fail = core_package_refs (failure_core fail) ;
  rejected_fixture_package_refs_own_visit :
    failure_package_refs fail
    = program_package_refs_from_visit (index (failure_input fail)) (input_visit (failure_input fail)) ;

  (* ── layout and plan: the canonical values that failed decision used ── *)
  rejected_fixture_layout : failure_layout fail = root_layout deep_fail_program ;
  rejected_fixture_plan : failure_plan fail = fresh_build_plan deep_fail_program ;

  (* ── the retained FAILED work forest is the real one: five members, four conversions and the leaf ── *)
  rejected_fixture_forest : length (forest_items (phase_work (phase (failure_core fail)))) = 5%nat ;

  (* ── the retained index and outcome domain, exact over the COMPLETE forest ── *)
  rejected_fixture_index_exact :
    forall k w,
      Index.KeyMap.find k (index_map (forest_index (phase_work (phase (failure_core fail))))) = Some w
      <-> (In w (forest_items (phase_work (phase (failure_core fail))))
           /\ Index.Snapshot.node_ref_key (work_node_ref w) = k) ;
  rejected_fixture_outcomes :
    forall k,
      Index.KeyMap.find k (outcomes_map (phase_ot (phase (failure_core fail)))) <> None
      <-> exists w, In w (forest_items (phase_work (phase (failure_core fail))))
                 /\ Index.Snapshot.node_ref_key (work_node_ref w) = k ;

  (* ── the retained trace explains EVERY member's position ── *)
  rejected_fixture_trace :
    forall wm : WorkMember (phase_work (phase (failure_core fail))),
      exists prefix,
        forest_items (phase_work (phase (failure_core fail)))
        = prefix ++ proj1_sig wm
                    :: projT1 (total_forest_outcome_cause (phase_ot (phase (failure_core fail))) wm) ;

  (* the innermost failure's exact retained cause, down to the one rejecting conversion *)
  rejected_fixture_innermost_cause : deep_fail_innermost_diag_claim (failure_core fail) ;

  (* every enclosing conversion is a child failure with no reason of its own, over its own cause *)
  rejected_fixture_outer_causes :
    deep_fail_outer_childfail_claim (failure_input fail) (failure_phase fail) ;

  (* ── and the rejection is real: the retained core's own final list is non-empty ── *)
  rejected_fixture_rejected : failure_diagnostics fail <> nil
}.

(** the ONE rejected root theorem. *)
Theorem deep_fail_compile_fixture :
  exists fail,
    compile deep_fail_program = Rejected fail
    /\ RejectedFixture fail.
Proof.
  destruct (compile_rejected_of_inadmissible deep_fail_program
              (reject_no_compile deep_fail_program ltac:(vm_compute; reflexivity))) as [fail Hc].
  exists fail. split; [ exact Hc | ].
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (core_refs_fold_own_visit _ (failure_core fail)).
  - exact (core_layout_exact (failure_core fail)).
  - exact (core_plan_is_fresh_build_plan (failure_core fail)).
  - rewrite (core_work_count_source (failure_core fail)), keyed_visit_source. vm_compute. reflexivity.
  - exact (index_exact (forest_index (phase_work (phase (failure_core fail))))).
  - exact (outcomes_domain_iff_forest (phase_ot (phase (failure_core fail)))).
  - intro wm.
    destruct (total_forest_outcome_cause (phase_ot (phase (failure_core fail))) wm)
      as [rest [acc_rest [[Hsplit Hstep] Hpreserve]]].
    cbn [projT1]. exact Hsplit.
  - exact (deep_fail_innermost_diag (failure_core fail)).
  - exact (deep_fail_outer_childfail _ _).
  - exact (failure_nonempty fail).
Qed.

(* the production table admits no foreign key and no wrong-kind key *)
Theorem phase_domain_exact (p : Syntax.Program) :
  let input := build_compilation_input p (Index.index_program p) in
  let ph := build_expression_phase input in
  (forall k, Index.KeyMap.find k (outcomes_map (phase_ot ph)) <> None ->
     exists w, In w (forest_items (phase_work ph)) /\ Index.Snapshot.node_ref_key (work_node_ref w) = k)
  /\ (forall r occ, In (r, occ) (input_visit input) -> Index.view_expr occ = None ->
       Index.KeyMap.find (Index.Snapshot.node_ref_key r) (outcomes_map (phase_ot ph)) = None).
Proof.
  cbn zeta. split.
  - intros k Hk. exact (proj1 (outcomes_domain_iff_forest (phase_ot _) k) Hk).
  - intros r occ Hin Hv. exact (outcomes_nonexpr_absent (phase_ot _) r occ Hin Hv).
Qed.

(** each rejected program yields exactly one diagnostic, with its code, its anchor and its payload *)
Definition over_default_int_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 9223372036854775808 ] ] ].
Theorem over_default_int_erased :
  erased_report over_default_int_program (Index.Snapshot.index_program over_default_int_program)
  = [ MakeErased CodeDefaultNotRepresentable (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* default float overflow: a bare finite decimal outside finite [float64]. *)
Definition over_default_float_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.FloatLiteral (Float.MakeDecimal 1 400 eq_refl) ] ] ].
Theorem over_default_float_erased :
  erased_report over_default_float_program (Index.Snapshot.index_program over_default_float_program)
  = [ MakeErased CodeDefaultNotRepresentable (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.FloatType F64)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* default complex overflow: a bare complex whose component cannot default to [complex128]. *)
Definition over_default_complex_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 1 400 eq_refl) (Float.MakeDecimal 0 0 eq_refl)) ] ] ].
Theorem over_default_complex_erased :
  erased_report over_default_complex_program (Index.Snapshot.index_program over_default_complex_program)
  = [ MakeErased CodeDefaultNotRepresentable (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.ComplexType C128)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* an invalid explicit integer conversion, anchored at the conversion itself *)
Definition bad_int8_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128) ] ] ].
Theorem bad_int8_erased :
  erased_report bad_int8_program (Index.Snapshot.index_program bad_int8_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int8)) None (Some (Syntax.type_expr_of_name Names.Int8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* fractional float -> integer [int(3.5)]: anchored at the conversion. *)
Definition frac_f2i_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral (Float.MakeDecimal 35 (-1) eq_refl)) ] ] ].
Theorem frac_f2i_erased :
  erased_report frac_f2i_program (Index.Snapshot.index_program frac_f2i_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int)) None (Some (Syntax.type_expr_of_name Names.Int)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* nonzero-imaginary complex -> scalar [int(complex(3,1))]: anchored at the conversion. *)
Definition nz_c2s_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 3 0 eq_refl) (Float.MakeDecimal 1 0 eq_refl))) ] ] ].
Theorem nz_c2s_erased :
  erased_report nz_c2s_program (Index.Snapshot.index_program nz_c2s_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int)) None (Some (Syntax.type_expr_of_name Names.Int)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* wrong-kind conversion [int(true)]: anchored at the conversion, no generic unlocated typing error. *)
Definition wrongkind_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.BoolLiteral true) ] ] ].
Theorem wrongkind_erased :
  erased_report wrongkind_program (Index.Snapshot.index_program wrongkind_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int)) None (Some (Syntax.type_expr_of_name Names.Int)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** two aliases resolving to one semantic target still carry different erased source targets *)
Definition bad_byte256_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Byte) (Syntax.IntegerLiteral 256) ] ] ].
Definition bad_uint8_256_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 256) ] ] ].
Theorem bad_byte256_erased :
  erased_report bad_byte256_program (Index.Snapshot.index_program bad_byte256_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Uint8)) None (Some (Syntax.type_expr_of_name Names.Byte)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem bad_uint8_256_erased :
  erased_report bad_uint8_256_program (Index.Snapshot.index_program bad_uint8_256_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Uint8)) None (Some (Syntax.type_expr_of_name Names.Uint8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem byte_uint8_erased_differ :
  erased_report bad_byte256_program (Index.Snapshot.index_program bad_byte256_program)
  <> erased_report bad_uint8_256_program (Index.Snapshot.index_program bad_uint8_256_program).
Proof.
  intro H. rewrite bad_byte256_erased, bad_uint8_256_erased in H.
  apply tsyn_byte_neq_uint8. congruence.
Qed.

Definition bad_rune_over_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Rune) (Syntax.IntegerLiteral 2147483648) ] ] ].
Definition bad_int32_over_program := singleton_program c3_ms (FilePath.Make "main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 2147483648) ] ] ].
Theorem bad_rune_over_erased :
  erased_report bad_rune_over_program (Index.Snapshot.index_program bad_rune_over_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int32)) None (Some (Syntax.type_expr_of_name Names.Rune)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem bad_int32_over_erased :
  erased_report bad_int32_over_program (Index.Snapshot.index_program bad_int32_over_program)
  = [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "main.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int32)) None (Some (Syntax.type_expr_of_name Names.Int32)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem rune_int32_erased_differ :
  erased_report bad_rune_over_program (Index.Snapshot.index_program bad_rune_over_program)
  <> erased_report bad_int32_over_program (Index.Snapshot.index_program bad_int32_over_program).
Proof.
  intro H. rewrite bad_rune_over_erased, bad_int32_over_erased in H.
  apply tsyn_rune_neq_int32. congruence.
Qed.

(** duplicate mains across files: the report names the canonical later main, in path order *)
Theorem dup_across_files_erased :
  option_map (fun p => erased_report_src (Syntax.files p))
             (build_program c3_ms [ main_file_node (FilePath.Make "a.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ] ]
                                  ; main_file_node (FilePath.Make "b.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ] ] ])
  = Some [ MakeErased CodeMainRedeclared (AnchorNode (Index.MakeKey (FilePath.Make "b.go" eq_refl) 3%positive))
             [ AnchorNode (Index.MakeKey (FilePath.Make "a.go" eq_refl) 3%positive) ] None None None ].
Proof. vm_compute. reflexivity. Qed.

(** four simultaneous failures across four packages, and the whole erased report is exactly those four *)
Theorem simultaneous_failures_erased :
  option_map (fun p => erased_report_src (Syntax.files p))
     (build_program c3_ms
        [ main_file_node (FilePath.Make "a/x.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128) ] ] ]
        ; main_file_node (FilePath.Make "b/y.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral (Float.MakeDecimal 35 (-1) eq_refl)) ] ] ]
        ; main_file_node (FilePath.Make "c/p.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ] ]
        ; main_file_node (FilePath.Make "c/q.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ] ]
        ; main_file_node (FilePath.Make "d/z.go" eq_refl) [ ] ])
  = Some [ MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "a/x.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int8)) None (Some (Syntax.type_expr_of_name Names.Int8))
         ; MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "b/y.go" eq_refl) 5%positive)) [] (Some (Typing.IntegerType Integer.Int)) None (Some (Syntax.type_expr_of_name Names.Int))
         ; MakeErased CodeMainRedeclared (AnchorNode (Index.MakeKey (FilePath.Make "c/q.go" eq_refl) 3%positive))
             [ AnchorNode (Index.MakeKey (FilePath.Make "c/p.go" eq_refl) 3%positive) ] None None None
         ; MakeErased CodeMissingMainEntry (AnchorPackage "d") [] None None None ].
Proof. vm_compute. reflexivity. Qed.

(** the canonical report orders both node-anchored diagnostics by key, whatever their discovery order *)
Theorem mixed_order_erased :
  option_map (fun p => erased_report_src (Syntax.files p))
     (build_program c3_ms
        [ main_file_node (FilePath.Make "a/p.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ] ]
        ; main_file_node (FilePath.Make "a/q.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ] ]
        ; main_file_node (FilePath.Make "z/main.go" eq_refl) [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128) ] ] ] ])
  = Some [ MakeErased CodeMainRedeclared (AnchorNode (Index.MakeKey (FilePath.Make "a/q.go" eq_refl) 3%positive))
             [ AnchorNode (Index.MakeKey (FilePath.Make "a/p.go" eq_refl) 3%positive) ] None None None
         ; MakeErased CodeInvalidConversion (AnchorNode (Index.MakeKey (FilePath.Make "z/main.go" eq_refl) 5%positive))
             [] (Some (Typing.IntegerType Integer.Int8)) None (Some (Syntax.type_expr_of_name Names.Int8)) ].
Proof. vm_compute. reflexivity. Qed.

(* the fixtures spell strings directly, so the string scope reopens here *)
Local Open Scope string_scope.

(** the build-output fixtures, computed directly where the surface is index-free *)

Definition ex_ms : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "example.com/m" eq_refl) Version.Go1_23.
Definition ex_main : list Syntax.Decl := [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ] ].
(* a package-local SEMANTIC error: uint8(int(300)) — the inner int(300) is valid, the outer uint8 is not. *)
Definition ex_bad  : list Syntax.Decl := [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.IntegerLiteral 300)) ] ] ].

(* 20.1 — EMPTY IMAGE: no packages -> NoPackages, preflight succeeds vacuously, Admissible, no diagnostics. *)
Example empty_image_plan      : fresh_build_plan (empty_program ex_ms) = NoPackages.                    Proof. vm_compute. reflexivity. Qed.
Example empty_image_preflight : fresh_build_disposition_ok (fresh_build_plan (empty_program ex_ms)) = true. Proof. vm_compute. reflexivity. Qed.
Example empty_image_admissible : Admissible (empty_program ex_ms).                Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.
Example empty_image_report    : forall idx, elaboration_diagnostics (empty_program ex_ms) idx = nil.
Proof. intro idx. apply (proj2 (elaboration_diagnostics_nil_iff_admissible _ idx)). exact empty_image_admissible. Qed.

(* one valid root package whose output name is absent from the fresh root, so the preflight succeeds *)
Definition fixture_root : Syntax.Program := singleton_program ex_ms (FilePath.Make "main.go" eq_refl) ex_main.
Example root_main_absent_output_plan      : fresh_build_plan fixture_root = WriteSingleMain "" "example.com/m" "m" None.   Proof. vm_compute. reflexivity. Qed.
Example root_main_absent_output_preflight : fresh_build_disposition_ok (fresh_build_plan fixture_root) = true.               Proof. vm_compute. reflexivity. Qed.
Example root_main_absent_output_admissible : Admissible fixture_root.                              Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* a sole immediate child whose output name is an existing root directory, so the preflight fails *)
Definition fixture_sub : Syntax.Program := singleton_program ex_ms (FilePath.Make "sub/main.go" eq_refl) ex_main.
Example child_package_output_collision_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fixture_sub) = false.   Proof. vm_compute. reflexivity. Qed.
Example child_package_output_collision_inadmissible   : ~ Admissible fixture_sub.
Proof. intros [Hpf _]. unfold fresh_build_preflight_ok in Hpf. vm_compute in Hpf. discriminate. Qed.
Example child_package_output_collision_report : forall idx, exists pk name, elaboration_diagnostics fixture_sub idx = [BuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.

(* the same collision beside a semantic error: the report stays the build-output one, by precedence *)
Definition fixture_sub_err : Syntax.Program := singleton_program ex_ms (FilePath.Make "sub/main.go" eq_refl) ex_bad.
Example collision_hides_semantic_error_untyped : program_typedb fixture_sub_err = false.                                        Proof. vm_compute. reflexivity. Qed.
Example collision_hides_semantic_error_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fixture_sub_err) = false. Proof. vm_compute. reflexivity. Qed.
Example collision_hides_semantic_error_report_hides_semantic : forall idx, exists pk name, elaboration_diagnostics fixture_sub_err idx = [BuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.

(* a deeper package whose output name is not the root directory, so the preflight succeeds *)
Definition fixture_ab : Syntax.Program := singleton_program ex_ms (FilePath.Make "a/b/main.go" eq_refl) ex_main.
Example deep_package_absent_output_preflight : fresh_build_disposition_ok (fresh_build_plan fixture_ab) = true. Proof. vm_compute. reflexivity. Qed.
Example deep_package_absent_output_admissible : Admissible fixture_ab.                Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* a final version element is stripped, so the output name collides with the existing root directory *)
Definition fixture_av2 : Syntax.Program := singleton_program ex_ms (FilePath.Make "a/v2/main.go" eq_refl) ex_main.
Example final_v2_package_collision_output_a       : fresh_build_plan fixture_av2 = WriteSingleMain "a/v2" "example.com/m/a/v2" "a" (Some DirectoryEntry). Proof. vm_compute. reflexivity. Qed.
Example final_v2_package_collision_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fixture_av2) = false. Proof. vm_compute. reflexivity. Qed.
Example final_v2_package_collision_inadmissible   : ~ Admissible fixture_av2.
Proof. intros [Hpf _]. unfold fresh_build_preflight_ok in Hpf. vm_compute in Hpf. discriminate. Qed.
(* the erased report carries the exact colliding name, so a different collision compares unequal *)
Example final_v2_package_collision_erased_output :
  map erase_diagnostic (fresh_build_diagnostics fixture_av2)
  = [ MakeErased CodeBuildOutputIsDirectory (AnchorPackage "a/v2") [] None (Some "a") None ].
Proof. vm_compute. reflexivity. Qed.

(* an immediate version element strips to the module basename, which does not collide *)
Definition fixture_v2 : Syntax.Program := singleton_program ex_ms (FilePath.Make "v2/main.go" eq_refl) ex_main.
Example immediate_v2_package_no_collision_output_m   : fresh_build_plan fixture_v2 = WriteSingleMain "v2" "example.com/m/v2" "m" None. Proof. vm_compute. reflexivity. Qed.
Example immediate_v2_package_no_collision_preflight  : fresh_build_disposition_ok (fresh_build_plan fixture_v2) = true. Proof. vm_compute. reflexivity. Qed.
Example immediate_v2_package_no_collision_admissible  : Admissible fixture_v2.               Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* multiple main packages discard the default output, so no preflight failure arises *)
Example multiple_main_packages_discard_outputs : forall p,
  build_program ex_ms [ main_file_node (FilePath.Make "a/main.go" eq_refl) ex_main
                      ; main_file_node (FilePath.Make "b/main.go" eq_refl) ex_main ] = Some p ->
  fresh_build_plan p = DiscardMultiple 2
  /\ fresh_build_disposition_ok (fresh_build_plan p) = true
  /\ Admissible p.
Proof.
  intros p H. vm_compute in H. injection H as <-.
  split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | apply admissible_of_source_spec_valid_b; vm_compute; reflexivity ] ].
Qed.

(* with no collision branch the semantic diagnostics are exposed, and the class is the typing one *)
Example multiple_packages_expose_semantic_failure : forall p,
  build_program ex_ms [ main_file_node (FilePath.Make "a/main.go" eq_refl) ex_main
                      ; main_file_node (FilePath.Make "b/main.go" eq_refl) ex_bad ] = Some p ->
  fresh_build_disposition_ok (fresh_build_plan p) = true
  /\ map erased_code (erased_report p (Index.Snapshot.index_program p)) = [CodeInvalidConversion].
Proof.
  intros p H. vm_compute in H. injection H as <-.
  split; [ vm_compute; reflexivity | rewrite erased_report_src_eq; vm_compute; reflexivity ].
Qed.

(* an output name of "go.mod" targets the regular go.mod, so the preflight succeeds and records it *)
Definition ex_ms_gomod : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "example.com/go.mod" eq_refl) Version.Go1_23.
Definition fixture_gomod : Syntax.Program := singleton_program ex_ms_gomod (FilePath.Make "main.go" eq_refl) ex_main.
Example go_module_overwrite_plan      : fresh_build_plan fixture_gomod = WriteSingleMain "" "example.com/go.mod" "go.mod" (Some GoModuleEntry). Proof. vm_compute. reflexivity. Qed.
Example go_module_overwrite_preflight : fresh_build_disposition_ok (fresh_build_plan fixture_gomod) = true. Proof. vm_compute. reflexivity. Qed.
Example go_module_overwrite_admissible : Admissible fixture_gomod.             Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* an output name matching a root source file targets a regular file, so the preflight succeeds *)
Definition ex_ms_srcname : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "example.com/main.go" eq_refl) Version.Go1_23.
Definition fixture_srcov : Syntax.Program := singleton_program ex_ms_srcname (FilePath.Make "main.go" eq_refl) ex_main.
Example source_file_overwrite_preflight : fresh_build_disposition_ok (fresh_build_plan fixture_srcov) = true. Proof. vm_compute. reflexivity. Qed.
Example source_file_overwrite_admissible : Admissible fixture_srcov.             Proof. apply admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* the target lookup is exact string identity, so a partial match is not a collision *)
Example output_name_exact_noncollision : PackageMap.find "m" (root_layout fixture_root) = None. Proof. vm_compute. reflexivity. Qed.

(* three mains in one package: a collision hides both redeclarations, and no collision exposes them *)
Definition ex_3main : list Syntax.Decl :=
  [ Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 1 ] ]; Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 2 ] ]; Syntax.Main [ Syntax.Println [ Syntax.IntegerLiteral 3 ] ] ].
Definition three_main_redeclarations_hidden : Syntax.Program := singleton_program ex_ms (FilePath.Make "sub/main.go" eq_refl) ex_3main.
Definition three_main_redeclarations_exposed  : Syntax.Program := singleton_program ex_ms (FilePath.Make "main.go" eq_refl)     ex_3main.
Example three_main_redeclarations_hidden_report : forall idx, exists pk name, elaboration_diagnostics three_main_redeclarations_hidden idx = [BuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.
Example three_main_redeclarations_exposed_report :
  map erased_code (erased_report three_main_redeclarations_exposed
                    (Index.Snapshot.index_program three_main_redeclarations_exposed))
  = [CodeMainRedeclared; CodeMainRedeclared].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* a missing main entry, hidden behind a collision and exposed without one *)
Definition fixture_nomain_hidden : Syntax.Program := singleton_program ex_ms (FilePath.Make "sub/main.go" eq_refl) nil.
Definition fixture_nomain_shown  : Syntax.Program := singleton_program ex_ms (FilePath.Make "main.go" eq_refl)     nil.
Example missing_main_hidden_report : forall idx, exists pk name,
  elaboration_diagnostics fixture_nomain_hidden idx = [BuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.
Example missing_main_exposed_report :
  map erased_code (erased_report fixture_nomain_shown
                    (Index.Snapshot.index_program fixture_nomain_shown)) = [CodeMissingMainEntry].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* a reordered construction under one module spec gives an equal plan, report and class *)
Theorem reordered_construction_determinism_full_determinism :
  forall p1 p2 (idx1 : Index.Snapshot.Syntax p1) (idx2 : Index.Snapshot.Syntax p2),
    build_program c3_ms [rnode_a; rnode_b] = Some p1 ->
    build_program c3_ms [rnode_b; rnode_a] = Some p2 ->
    fresh_build_plan p1 = fresh_build_plan p2
    /\ erased_elaboration_report p1 idx1 = erased_elaboration_report p2 idx2.
Proof.
  intros p1 p2 idx1 idx2 H1 H2.
  assert (HIE : ProgramInputEqual p1 p2).
  { unfold build_program in H1, H2.
    destruct (Syntax.files_of_nodes [rnode_a; rnode_b]) as [fm1|] eqn:F1; [ | discriminate ].
    destruct (Syntax.files_of_nodes [rnode_b; rnode_a]) as [fm2|] eqn:F2; [ | discriminate ].
    injection H1 as <-. injection H2 as <-. split; [ reflexivity | cbn [Syntax.files] ].
    exact (Syntax.files_of_nodes_permutation _ _ fm1 fm2 (perm_swap rnode_b rnode_a []) F1 F2). }
  split; [ exact (fresh_build_plan_input_equal _ _ HIE)
         | exact (erased_elaboration_report_input_equal _ _ idx1 idx2 HIE) ].
Qed.

(* equal files under different module specs give different plans, so file equality alone is not enough *)
Definition fixture_cex_1 : Syntax.Program := singleton_program ex_ms (FilePath.Make "v2/main.go" eq_refl) ex_main.
Definition fixture_cex_2 : Syntax.Program :=
  singleton_program (Syntax.MakeModuleSpec (ModulePath.Make "example.com/other" eq_refl) Version.Go1_23) (FilePath.Make "v2/main.go" eq_refl) ex_main.
Example equal_files_different_modules_files_equal : Syntax.FilesEqual (Syntax.files fixture_cex_1) (Syntax.files fixture_cex_2).
Proof. assert (Syntax.files fixture_cex_1 = Syntax.files fixture_cex_2) as Heq by (vm_compute; reflexivity).
       rewrite Heq. apply Syntax.files_equal_refl. Qed.
Example equal_files_different_modules_plans_differ : fresh_build_plan fixture_cex_1 <> fresh_build_plan fixture_cex_2.
Proof. vm_compute. discriminate. Qed.

