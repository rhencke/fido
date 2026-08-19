(* PackageIdentity — file, package, and selected-nonempty-package identity only; no main, collision, or issue. *)

From Stdlib Require Import String Ascii Bool Arith PeanoNat Lia List.
From Fido Require Import Index FilePath Syntax ModulePath.
Import ListNotations.

(* a file is nonempty when it holds at least one top-level declaration (more than just its file occurrence) *)
Definition nonempty_file {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) : bool :=
  Nat.ltb 1 (Index.occ_count fr).

(* the retained package surface: every distinct file directory, in stable file order *)
Definition surface_dirs {p} (idx : Index.ProgramIndex p) : list FilePath.PkgDir :=
  nodup FilePath.pkgdir_eq_dec (map (fun fr => FilePath.file_dir (Index.fr_path fr)) (Index.all_files idx)).

Definition PackageSurface {p} (idx : Index.ProgramIndex p) : Type :=
  { l : list FilePath.PkgDir | l = surface_dirs idx }.
Definition package_surface {p} (idx : Index.ProgramIndex p) : PackageSurface idx :=
  exist _ (surface_dirs idx) eq_refl.
Definition surf {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : list FilePath.PkgDir := proj1_sig s.
Definition package_count {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : nat := length (surf s).

Record PackageRef {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : Type := package_at {
  pr_pos : nat ;
  pr_lt  : pr_pos < package_count s
}.
Arguments package_at {p idx s} _ _.
Arguments pr_pos {p idx s} _.
Arguments pr_lt {p idx s} _.

Definition pkg_dir {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : FilePath.PkgDir :=
  Index.nth_lt (surf s) (pr_pos pr) (pr_lt pr).
Definition pkg_components {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : list String.string :=
  FilePath.pkg_components (pkg_dir pr).

Definition pkgdir_eqb (a b : FilePath.PkgDir) : bool := if FilePath.pkgdir_eq_dec a b then true else false.

(* the files whose directory is this package's directory *)
Definition pkg_members {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s)
  : list (Index.FileRef idx) :=
  filter (fun fr => pkgdir_eqb (FilePath.file_dir (Index.fr_path fr)) (pkg_dir pr)) (Index.all_files idx).

Fixpoint first_index (d : FilePath.PkgDir) (l : list FilePath.PkgDir) : nat :=
  match l with
  | [] => 0
  | x :: xs => if FilePath.pkgdir_eq_dec x d then 0 else S (first_index d xs)
  end.

Lemma first_index_lt : forall d l, In d l -> first_index d l < length l.
Proof.
  induction l as [|x xs IH]; intro Hin; cbn [first_index length].
  - destruct Hin.
  - destruct (FilePath.pkgdir_eq_dec x d) as [E|NE]; [lia|].
    destruct Hin as [Heq|Hin]; [contradiction (NE Heq)|]. specialize (IH Hin); lia.
Qed.

Lemma first_index_nth : forall d l, In d l -> nth_error l (first_index d l) = Some d.
Proof.
  induction l as [|x xs IH]; intro Hin; cbn [first_index].
  - destruct Hin.
  - destruct (FilePath.pkgdir_eq_dec x d) as [E|NE]; [cbn [nth_error]; rewrite E; reflexivity|].
    destruct Hin as [Heq|Hin]; [contradiction (NE Heq)|]. cbn [nth_error]. apply IH; exact Hin.
Qed.

Lemma nth_lt_In {A} (l : list A) i (H : i < length l) : In (Index.nth_lt l i H) l.
Proof. apply nth_error_In with (n := i). apply Index.nth_lt_nth_error. Qed.

Lemma first_index_nth_nodup : forall (l : list FilePath.PkgDir), NoDup l ->
  forall i (H : i < length l), first_index (Index.nth_lt l i H) l = i.
Proof.
  induction l as [|x xs IH]; intros Hnd [|k] H; cbn [Index.nth_lt first_index length] in *.
  - exfalso; exact (Nat.nlt_0_r 0 H).
  - exfalso; exact (Nat.nlt_0_r (S k) H).
  - destruct (FilePath.pkgdir_eq_dec x x) as [E|NE]; [reflexivity | contradiction (NE eq_refl)].
  - inversion Hnd as [|x0 xs0 Hnin Hnd0 Heql]; subst.
    destruct (FilePath.pkgdir_eq_dec x (Index.nth_lt xs k (proj2 (Nat.succ_lt_mono k (length xs)) H))) as [E|NE].
    + exfalso; apply Hnin; rewrite E; apply nth_lt_In.
    + f_equal. apply IH; exact Hnd0.
Qed.

(* all_files covers every member path, so every file directory sits in the surface *)
Lemma all_files_covers {p} (idx : Index.ProgramIndex p) (fr : Index.FileRef idx) :
  exists fr', In fr' (Index.all_files idx) /\ Index.fr_path fr' = Index.fr_path fr.
Proof.
  pose proof (Index.fr_in fr) as Hmem.
  apply Collections.FileFacts.mem_in_iff in Hmem. destruct Hmem as [fi Hmt].
  apply Collections.FileFacts.elements_mapsto_iff in Hmt.
  apply SetoidList.InA_alt in Hmt. destruct Hmt as [[k v] [Heq Hin]].
  destruct Heq as [Hk _]; cbn in Hk.
  assert (Hpath : k = Index.fr_path fr) by (symmetry; exact Hk).
  assert (Hfhk : Index.file_has idx k = true)
    by (unfold Index.file_has; rewrite Hpath; exact (Index.fr_in fr)).
  destruct (Index.mk_fileref_some idx k Hfhk) as [fr' Emk].
  exists fr'. split.
  - unfold Index.all_files. apply in_flat_map. exists (k, v). split.
    + exact Hin.
    + cbn [fst]. rewrite Emk. apply in_eq.
  - rewrite (Index.mk_fileref_path idx k fr' Emk). exact Hpath.
Qed.

Lemma file_dir_in_surface {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) :
  In (FilePath.file_dir (Index.fr_path fr)) (surface_dirs idx).
Proof.
  unfold surface_dirs. rewrite nodup_In. apply in_map_iff.
  destruct (all_files_covers idx fr) as [fr' [Hin Hp]]. exists fr'; split; [ rewrite Hp; reflexivity | exact Hin ].
Qed.

Lemma pof_lt {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (fr : Index.FileRef idx) :
  first_index (FilePath.file_dir (Index.fr_path fr)) (surf s) < package_count s.
Proof.
  unfold package_count. apply first_index_lt. unfold surf; rewrite (proj2_sig s). apply file_dir_in_surface.
Qed.

Definition package_of_file {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (fr : Index.FileRef idx)
  : PackageRef s := package_at (first_index (FilePath.file_dir (Index.fr_path fr)) (surf s)) (pof_lt s fr).

Definition mk_packageref {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (n : nat) : option (PackageRef s) :=
  match lt_dec n (package_count s) with left H => Some (package_at n H) | right _ => None end.

Definition packages {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : list (PackageRef s) :=
  flat_map (fun n => match mk_packageref s n with Some pr => [pr] | None => [] end) (seq 0 (package_count s)).

Lemma pkgref_positional {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx} (a b : PackageRef s) :
  pr_pos a = pr_pos b -> a = b.
Proof. destruct a as [pa Ha], b as [pb Hb]; cbn; intro E; subst pb; f_equal; apply Index.lt_unique. Qed.

Lemma nodup_surf {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : NoDup (surf s).
Proof. unfold surf; rewrite (proj2_sig s). unfold surface_dirs. apply NoDup_nodup. Qed.

(* a file in a package's member set is classified back to that exact package *)
Lemma package_of_file_member {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx)
  (pr : PackageRef s) (fr : Index.FileRef idx) : In fr (pkg_members pr) -> package_of_file s fr = pr.
Proof.
  unfold pkg_members. intro Hin. apply filter_In in Hin. destruct Hin as [_ Hdir].
  unfold pkgdir_eqb in Hdir.
  destruct (FilePath.pkgdir_eq_dec (FilePath.file_dir (Index.fr_path fr)) (pkg_dir pr)) as [E|]; [|discriminate Hdir].
  apply pkgref_positional. unfold package_of_file; cbn [pr_pos].
  unfold pkg_dir in E. rewrite E. apply first_index_nth_nodup. apply nodup_surf.
Qed.

Lemma all_files_complete {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) :
  In fr (Index.all_files idx).
Proof.
  destruct (all_files_covers idx fr) as [fr' [Hin Hp]].
  pose proof (Index.fileref_positional fr' fr Hp) as E; subst fr'; exact Hin.
Qed.

Lemma pkg_dir_of_file {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (fr : Index.FileRef idx) :
  pkg_dir (package_of_file s fr) = FilePath.file_dir (Index.fr_path fr).
Proof.
  assert (Hd : In (FilePath.file_dir (Index.fr_path fr)) (surf s)).
  { unfold surf; rewrite (proj2_sig s); apply file_dir_in_surface. }
  unfold pkg_dir, package_of_file; cbn [pr_pos pr_lt].
  pose proof (Index.nth_lt_nth_error (surf s)
                (first_index (FilePath.file_dir (Index.fr_path fr)) (surf s)) (pof_lt s fr)) as Hnl.
  rewrite (first_index_nth _ _ Hd) in Hnl. injection Hnl as Hnl. symmetry; exact Hnl.
Qed.

Lemma pkg_members_of_file {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (fr : Index.FileRef idx) :
  In fr (pkg_members (package_of_file s fr)).
Proof.
  unfold pkg_members. apply filter_In. split; [ apply all_files_complete |].
  unfold pkgdir_eqb. rewrite pkg_dir_of_file.
  destruct (FilePath.pkgdir_eq_dec (FilePath.file_dir (Index.fr_path fr)) (FilePath.file_dir (Index.fr_path fr)))
    as [_|NE]; [ reflexivity | contradiction (NE eq_refl) ].
Qed.

Lemma packages_complete {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) (pr : PackageRef s) :
  In pr (packages s).
Proof.
  unfold packages. apply in_flat_map. exists (pr_pos pr). split.
  - apply in_seq. pose proof (pr_lt pr); lia.
  - unfold mk_packageref. destruct (lt_dec (pr_pos pr) (package_count s)) as [H|H].
    + replace (package_at (pr_pos pr) H) with pr by (apply pkgref_positional; reflexivity). left; reflexivity.
    + exfalso; apply H; exact (pr_lt pr).
Qed.

Lemma one_surface_retained {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) :
  surf s = surf (package_surface idx).
Proof. unfold surf, package_surface; cbn [proj1_sig]. exact (proj2_sig s). Qed.

Definition packageref_eq_dec {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : {a = b} + {a <> b}.
Proof.
  destruct (Nat.eq_dec (pr_pos a) (pr_pos b)) as [E|NE].
  - left; apply pkgref_positional; exact E.
  - right; intro H; apply NE; rewrite H; reflexivity.
Defined.
Definition packageref_eqb {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : bool := if packageref_eq_dec a b then true else false.
Lemma packageref_eqb_spec {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : packageref_eqb a b = true <-> a = b.
Proof. unfold packageref_eqb; destruct (packageref_eq_dec a b); split; congruence. Qed.

(* selected nonempty packages: those whose directory holds at least one nonempty file, in surface order *)
Definition is_selected {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : bool :=
  existsb nonempty_file (pkg_members pr).
Definition selected_packages {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : list (PackageRef s) :=
  filter is_selected (packages s).

Inductive PackageSelection {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : Type :=
| NoSelected : PackageSelection s
| OneSelected : PackageRef s -> PackageSelection s
| MultipleSelected : PackageRef s -> PackageRef s -> list (PackageRef s) -> PackageSelection s.
Arguments NoSelected {p idx s}.
Arguments OneSelected {p idx s} _.
Arguments MultipleSelected {p idx s} _ _ _.

Definition package_selection {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : PackageSelection s :=
  match selected_packages s with
  | [] => NoSelected
  | a :: nil => OneSelected a
  | a :: b :: rest => MultipleSelected a b rest
  end.

(* the complete import path is module-path components ++ package-directory components *)
Local Open Scope string_scope.

Definition module_components {p} (idx : Index.ProgramIndex p) : list string :=
  ModulePath.segments (Syntax.module_path (Syntax.module_spec p)).

Definition import_path {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (pr : PackageRef s) : list string := module_components idx ++ pkg_components pr.

Definition ascii_is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 48 n) (Nat.leb n 57).
Fixpoint str_all_digits (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (ascii_is_digit c) (str_all_digits s') end.
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
Definition default_exec_name_c (comps : list string) : string :=
  match comps with
  | _ :: _ :: _ =>
      let final := List.last comps ""%string in
      if is_version_element final then List.last (List.removelast comps) ""%string else final
  | _ => List.last comps ""%string
  end.
Definition default_exec_name {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (pr : PackageRef s) : string := default_exec_name_c (import_path pr).

(* the module-root entries that a fresh executable could collide with: the top-level directory of each package *)
Definition first_dir_component {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (pr : PackageRef s) : option string :=
  match pkg_components pr with c :: _ => Some c | [] => None end.
Definition root_entry_names {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : list string :=
  fold_right (fun pr acc => match first_dir_component pr with Some c => c :: acc | None => acc end) [] (packages s).

Local Close Scope string_scope.
