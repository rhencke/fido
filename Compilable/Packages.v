From Stdlib Require Import List Bool String Ascii Arith Lia Sorted Permutation NArith.
From Stdlib Require Import RelationClasses Morphisms.
From Fido Require Import Collections FilePath ModulePath Version Syntax.
Import ListNotations.

Definition decl_is_main (d : Syntax.TopLevelDecl) : bool :=
  match d with Syntax.Main _ => true | Syntax.TopDeclaration _ => false end.
Definition file_main_count (decls : list Syntax.TopLevelDecl) : nat := List.length (List.filter decl_is_main decls).

Module PackageMap := Collections.PackageMap.
Module PackageFacts := Collections.PackageFacts.
Module PackageProperties := Collections.PackageProperties.

(* A package summary carries only the live fact the fragment needs: its total `main` count. *)
Record PackageSummary : Type := MakePackageSummary { summary_main_count : nat }.
Definition summary_count (o : option PackageSummary) : nat := match o with Some s => summary_main_count s | None => 0 end.

Definition package_map_add_main (dir : string) (n : nat) (acc : PackageMap.t PackageSummary) : PackageMap.t PackageSummary :=
  PackageMap.add dir (MakePackageSummary (n + summary_count (PackageMap.find dir acc))) acc.
Definition package_step (path : FilePath.T) (sf : Syntax.File) (acc : PackageMap.t PackageSummary) : PackageMap.t PackageSummary :=
  package_map_add_main (FilePath.parent path) (file_main_count (Syntax.declarations sf)) acc.

(* One fold over the file map, each file contributing its count once, rather than a scan per file. *)
Definition package_summaries (fm : Syntax.Files) : PackageMap.t PackageSummary :=
  Syntax.FileMap.fold package_step fm (PackageMap.empty PackageSummary).

(* one canonical per-package main-count status: exactly-one, missing, or redeclared main. *)
Inductive PackageRuleStatus : Type := PackageOneMain | PackageMissingMain | PackageMainRedeclared.
Definition package_rule_status (cnt : nat) : PackageRuleStatus :=
  match cnt with O => PackageMissingMain | S O => PackageOneMain | S (S _) => PackageMainRedeclared end.
Definition package_rule_result (p : Syntax.Program) : list (string * PackageRuleStatus) :=
  List.map (fun ds => (fst ds, package_rule_status (summary_main_count (snd ds))))
           (PackageMap.elements (package_summaries (Syntax.files p))).

(* every package key in the one-pass summaries is some file binding's parent, proved over the fold, no list-scan. *)
Theorem package_no_empty : forall fm dir,
  PackageMap.In dir (package_summaries fm) ->
  exists b, In b (Syntax.file_bindings fm) /\ FilePath.parent (fst b) = dir.
Proof.
  intros fm dir Hin.
  assert (Hgen : exists k e, Syntax.FileMap.MapsTo k e fm /\ FilePath.parent k = dir).
  { revert Hin. unfold package_summaries.
    apply (Collections.FileProperties.fold_rec_bis
             (P := fun m acc =>
                   PackageMap.In dir acc ->
                   exists k e, Syntax.FileMap.MapsTo k e m /\ FilePath.parent k = dir)).
    - intros m1 m2 acc Heq IH Hacc. destruct (IH Hacc) as [k [e [Hmt Hpar]]].
      apply Syntax.FileFacts.find_mapsto_iff in Hmt. rewrite (Heq k) in Hmt.
      apply Syntax.FileFacts.find_mapsto_iff in Hmt.
      exists k, e. split; [ exact Hmt | exact Hpar ].
    - intro Hacc. apply PackageFacts.empty_in_iff in Hacc. destruct Hacc.
    - intros k e acc m' _ Hnin IH Hacc.
      unfold package_step, package_map_add_main in Hacc.
      apply PackageFacts.add_in_iff in Hacc. destruct Hacc as [Hd | Hacc].
      + exists k, e. split; [ apply Syntax.FileMap.add_1; reflexivity | exact Hd ].
      + destruct (IH Hacc) as [k' [e' [Hmt' Hpar']]].
        exists k', e'. split; [ | exact Hpar' ].
        apply Syntax.FileMap.add_2; [ | exact Hmt' ].
        intro Heqk. assert (Hkk : k = k') by exact Heqk. subst k'.
        apply Hnin. exists e'. exact Hmt'. }
  destruct Hgen as [k [e [Hmt Hpar]]]. exists (k, e). split; [ | cbn [fst]; exact Hpar ].
  unfold Syntax.file_bindings. apply Syntax.FileFacts.elements_mapsto_iff in Hmt.
  apply SetoidList.InA_alt in Hmt. destruct Hmt as [[k2 e2] [[Hk He] Hin2]].
  cbn in Hk, He. subst. exact Hin2.
Qed.

Local Open Scope string_scope.

Definition ascii_is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 48 n) (Nat.leb n 57).

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

Lemma default_exec_name_c_in : forall comps, comps <> [] -> In (default_exec_name_c comps) comps.
Proof.
  intros comps Hne. unfold default_exec_name_c. destruct comps as [|a [|b rest]]; [ contradiction | |].
  - cbn [List.last]. left; reflexivity.
  - destruct (is_version_element (List.last (a :: b :: rest) ""%string)).
    + apply removelast_in, last_in. cbn [List.removelast]. discriminate.
    + apply last_in. discriminate.
Qed.

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

Theorem package_import_path_deterministic : forall ms1 ms2 dir1 dir2,
  ms1 = ms2 -> dir1 = dir2 -> package_import_path ms1 dir1 = package_import_path ms2 dir2.
Proof. intros ms1 ms2 dir1 dir2 Hm Hd; subst; reflexivity. Qed.

(* the pattern selects exactly the domain of the one-pass package map *)

Definition selected_packages (p : Syntax.Program) : PackageMap.t PackageSummary := package_summaries (Syntax.files p).
Definition selected_package_keys (p : Syntax.Program) : list string := map fst (PackageMap.elements (selected_packages p)).
Definition selected_package_count (p : Syntax.Program) : nat := List.length (selected_package_keys p).

(* the fresh root layout: the go.mod, each root-level file, and one directory per nested first component *)

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

Lemma filename_ok_neq_gomod : forall f, FilePath.filename_ok f = true -> f <> "go.mod".
Proof. intros f Hf Heq. subst f. vm_compute in Hf. discriminate Hf. Qed.


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

(* every valid path contains a dot, because its last segment is a `.go` filename *)
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

(* the root layout as a standard string-keyed map, built by one fold and conflict-free by disjointness *)

Definition root_entry_of_file (b : FilePath.T * Syntax.File) : string * FreshRootEntryKind :=
  if String.eqb (FilePath.parent (fst b)) ""
  then (FilePath.text (fst b), SourceFileEntry (fst b))
  else (first_component (FilePath.text (fst b)), DirectoryEntry).

Definition root_layout (p : Syntax.Program) : PackageMap.t FreshRootEntryKind :=
  fold_right (fun b acc => PackageMap.add (fst (root_entry_of_file b)) (snd (root_entry_of_file b)) acc)
             (PackageMap.add "go.mod" GoModuleEntry (PackageMap.empty _))
             (Syntax.file_bindings (Syntax.files p)).

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

(* the retained build plan and its preflight, which fails before compiling on an existing directory *)

Inductive FreshBuildDisposition : Type :=
| NoPackages
| DiscardMultiple (count : nat)
| WriteSingleMain (dir import_path output_name : string) (target : option FreshRootEntryKind).

(* the plan as a pure function of the spec, the package keys and the layout, so retention derives it *)
Definition fresh_build_plan_of (ms : ModuleSpec) (keys : list string)
    (rl : PackageMap.t FreshRootEntryKind) : FreshBuildDisposition :=
  match keys with
  | [] => NoPackages
  | dir :: nil =>
      let ip := package_import_path ms dir in
      let ex := default_exec_name ms dir in
      WriteSingleMain dir ip ex (PackageMap.find ex rl)
  | _ :: _ :: _ => DiscardMultiple (List.length keys)
  end.

(* one plan builder, so the retained buckets reproduce it once their keys are shown equal *)
Definition fresh_build_plan (p : Syntax.Program) : FreshBuildDisposition :=
  fresh_build_plan_of (Syntax.module_spec p) (selected_package_keys p) (root_layout p).

Lemma selected_key_is_parent : forall p dir,
  In dir (selected_package_keys p) -> dir = ""%string \/ exists fp, FilePath.parent fp = dir.
Proof.
  intros p dir Hin. unfold selected_package_keys in Hin. apply in_map_iff in Hin.
  destruct Hin as [[k s] [Hfst Hinel]]. cbn in Hfst. subst k.
  assert (Hmt : PackageMap.MapsTo dir s (selected_packages p))
    by (apply PackageFacts.elements_mapsto_iff, SetoidList.InA_alt; exists (dir, s); split; [ split; reflexivity | exact Hinel ]).
  assert (Hex : exists b, In b (Syntax.file_bindings (Syntax.files p)) /\ FilePath.parent (fst b) = dir).
  { apply (package_no_empty (Syntax.files p) dir). exists s. exact Hmt. }
  destruct Hex as [b [_ Hpar]]. right. exists (fst b). exact Hpar.
Qed.

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

(* the EXACT zero / single / multiple plan CLASSIFICATION by selected-package count. *)
Lemma fresh_build_plan_zero : forall p,
  selected_package_keys p = [] -> fresh_build_plan p = NoPackages.
Proof. intros p H. unfold fresh_build_plan, fresh_build_plan_of. rewrite H. reflexivity. Qed.

Lemma fresh_build_plan_multiple : forall p d1 d2 rest,
  selected_package_keys p = d1 :: d2 :: rest ->
  fresh_build_plan p = DiscardMultiple (selected_package_count p).
Proof. intros p d1 d2 rest H. unfold fresh_build_plan, fresh_build_plan_of, selected_package_count. rewrite H. reflexivity. Qed.

(* the preflight decision: reject ONLY a sole-main default output name that is an existing root directory. *)
Definition fresh_build_disposition_ok (d : FreshBuildDisposition) : bool :=
  match d with
  | WriteSingleMain _ _ _ (Some DirectoryEntry) => false
  | _ => true
  end.

Definition fresh_build_preflight_ok (p : Syntax.Program) : Prop :=
  fresh_build_disposition_ok (fresh_build_plan p) = true.

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
