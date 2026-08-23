(* PackageIdentity — file, package, and selected-nonempty-package identity only; no main, collision, or issue. *)

From Stdlib Require Import String Ascii Bool Arith PeanoNat Lia List.
From Fido Require Import Index FilePath Syntax ModulePath.
Import ListNotations.

(* a file is nonempty when it holds at least one top-level declaration (more than just its file occurrence) *)
Definition nonempty_file {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx) : bool :=
  Nat.ltb 1 (Index.Core.occ_count fr).

(* the retained package surface: every distinct file directory, in stable file order *)
Definition surface_dirs {p} (idx : Index.Core.ProgramIndex p) : list FilePath.PkgDir :=
  nodup FilePath.pkgdir_eq_dec (map (fun fr => FilePath.file_dir (Index.Core.fr_path fr)) (Index.Edges.all_files idx)).

Definition PackageSurface {p} (idx : Index.Core.ProgramIndex p) : Type :=
  { l : list FilePath.PkgDir | l = surface_dirs idx }.
Definition package_surface {p} (idx : Index.Core.ProgramIndex p) : PackageSurface idx :=
  exist _ (surface_dirs idx) eq_refl.
Definition surf {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : list FilePath.PkgDir := proj1_sig s.
Definition package_count {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : nat := length (surf s).

Record PackageRef {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : Type := package_at {
  pr_pos : nat ;
  pr_lt  : pr_pos < package_count s
}.
Arguments package_at {p idx s} _ _.
Arguments pr_pos {p idx s} _.
Arguments pr_lt {p idx s} _.

Definition pkg_dir {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : FilePath.PkgDir :=
  Index.Model.nth_lt (surf s) (pr_pos pr) (pr_lt pr).
Definition pkg_components {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : list String.string :=
  FilePath.pkg_components (pkg_dir pr).

Definition pkgdir_eqb (a b : FilePath.PkgDir) : bool := if FilePath.pkgdir_eq_dec a b then true else false.

(* the files whose directory is this package's directory *)
Definition pkg_members {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s)
  : list (Index.Core.FileRef idx) :=
  filter (fun fr => pkgdir_eqb (FilePath.file_dir (Index.Core.fr_path fr)) (pkg_dir pr)) (Index.Edges.all_files idx).

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

Lemma nth_lt_In {A} (l : list A) i (H : i < length l) : In (Index.Model.nth_lt l i H) l.
Proof. apply nth_error_In with (n := i). apply Index.Model.nth_lt_nth_error. Qed.

Lemma first_index_nth_nodup : forall (l : list FilePath.PkgDir), NoDup l ->
  forall i (H : i < length l), first_index (Index.Model.nth_lt l i H) l = i.
Proof.
  induction l as [|x xs IH]; intros Hnd [|k] H; cbn [Index.Model.nth_lt first_index length] in *.
  - exfalso; exact (Nat.nlt_0_r 0 H).
  - exfalso; exact (Nat.nlt_0_r (S k) H).
  - destruct (FilePath.pkgdir_eq_dec x x) as [E|NE]; [reflexivity | contradiction (NE eq_refl)].
  - inversion Hnd as [|x0 xs0 Hnin Hnd0 Heql]; subst.
    destruct (FilePath.pkgdir_eq_dec x (Index.Model.nth_lt xs k (proj2 (Nat.succ_lt_mono k (length xs)) H))) as [E|NE].
    + exfalso; apply Hnin; rewrite E; apply nth_lt_In.
    + f_equal. apply IH; exact Hnd0.
Qed.

(* all_files covers every member path, so every file directory sits in the surface *)
Lemma all_files_covers {p} (idx : Index.Core.ProgramIndex p) (fr : Index.Core.FileRef idx) :
  exists fr', In fr' (Index.Edges.all_files idx) /\ Index.Core.fr_path fr' = Index.Core.fr_path fr.
Proof.
  pose proof (Index.Core.fr_in fr) as Hmem.
  apply Collections.FileFacts.mem_in_iff in Hmem. destruct Hmem as [fi Hmt].
  apply Collections.FileFacts.elements_mapsto_iff in Hmt.
  apply SetoidList.InA_alt in Hmt. destruct Hmt as [[k v] [Heq Hin]].
  destruct Heq as [Hk _]; cbn in Hk.
  assert (Hpath : k = Index.Core.fr_path fr) by (symmetry; exact Hk).
  assert (Hfhk : Index.Core.file_has idx k = true)
    by (unfold Index.Core.file_has; rewrite Hpath; exact (Index.Core.fr_in fr)).
  destruct (Index.Edges.mk_fileref_some idx k Hfhk) as [fr' Emk].
  exists fr'. split.
  - unfold Index.Edges.all_files. apply in_flat_map. exists (k, v). split.
    + exact Hin.
    + cbn [fst]. rewrite Emk. apply in_eq.
  - rewrite (Index.Edges.mk_fileref_path idx k fr' Emk). exact Hpath.
Qed.

Lemma file_dir_in_surface {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx) :
  In (FilePath.file_dir (Index.Core.fr_path fr)) (surface_dirs idx).
Proof.
  unfold surface_dirs. rewrite nodup_In. apply in_map_iff.
  destruct (all_files_covers idx fr) as [fr' [Hin Hp]]. exists fr'; split; [ rewrite Hp; reflexivity | exact Hin ].
Qed.

Lemma pof_lt {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (fr : Index.Core.FileRef idx) :
  first_index (FilePath.file_dir (Index.Core.fr_path fr)) (surf s) < package_count s.
Proof.
  unfold package_count. apply first_index_lt. unfold surf; rewrite (proj2_sig s). apply file_dir_in_surface.
Qed.

Definition package_of_file {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (fr : Index.Core.FileRef idx)
  : PackageRef s := package_at (first_index (FilePath.file_dir (Index.Core.fr_path fr)) (surf s)) (pof_lt s fr).

Definition mk_packageref {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (n : nat) : option (PackageRef s) :=
  match lt_dec n (package_count s) with left H => Some (package_at n H) | right _ => None end.

Definition packages {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : list (PackageRef s) :=
  flat_map (fun n => match mk_packageref s n with Some pr => [pr] | None => [] end) (seq 0 (package_count s)).

Lemma pkgref_positional {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx} (a b : PackageRef s) :
  pr_pos a = pr_pos b -> a = b.
Proof. destruct a as [pa Ha], b as [pb Hb]; cbn; intro E; subst pb; f_equal; apply Index.Model.lt_unique. Qed.

Lemma nodup_surf {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : NoDup (surf s).
Proof. unfold surf; rewrite (proj2_sig s). unfold surface_dirs. apply NoDup_nodup. Qed.

(* a file in a package's member set is classified back to that exact package *)
Lemma package_of_file_member {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx)
  (pr : PackageRef s) (fr : Index.Core.FileRef idx) : In fr (pkg_members pr) -> package_of_file s fr = pr.
Proof.
  unfold pkg_members. intro Hin. apply filter_In in Hin. destruct Hin as [_ Hdir].
  unfold pkgdir_eqb in Hdir.
  destruct (FilePath.pkgdir_eq_dec (FilePath.file_dir (Index.Core.fr_path fr)) (pkg_dir pr)) as [E|]; [|discriminate Hdir].
  apply pkgref_positional. unfold package_of_file; cbn [pr_pos].
  unfold pkg_dir in E. rewrite E. apply first_index_nth_nodup. apply nodup_surf.
Qed.

Lemma all_files_complete {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx) :
  In fr (Index.Edges.all_files idx).
Proof.
  destruct (all_files_covers idx fr) as [fr' [Hin Hp]].
  pose proof (Index.Edges.fileref_positional fr' fr Hp) as E; subst fr'; exact Hin.
Qed.

Lemma pkg_dir_of_file {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (fr : Index.Core.FileRef idx) :
  pkg_dir (package_of_file s fr) = FilePath.file_dir (Index.Core.fr_path fr).
Proof.
  assert (Hd : In (FilePath.file_dir (Index.Core.fr_path fr)) (surf s)).
  { unfold surf; rewrite (proj2_sig s); apply file_dir_in_surface. }
  unfold pkg_dir, package_of_file; cbn [pr_pos pr_lt].
  pose proof (Index.Model.nth_lt_nth_error (surf s)
                (first_index (FilePath.file_dir (Index.Core.fr_path fr)) (surf s)) (pof_lt s fr)) as Hnl.
  rewrite (first_index_nth _ _ Hd) in Hnl. injection Hnl as Hnl. symmetry; exact Hnl.
Qed.

Lemma pkg_members_of_file {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (fr : Index.Core.FileRef idx) :
  In fr (pkg_members (package_of_file s fr)).
Proof.
  unfold pkg_members. apply filter_In. split; [ apply all_files_complete |].
  unfold pkgdir_eqb. rewrite pkg_dir_of_file.
  destruct (FilePath.pkgdir_eq_dec (FilePath.file_dir (Index.Core.fr_path fr)) (FilePath.file_dir (Index.Core.fr_path fr)))
    as [_|NE]; [ reflexivity | contradiction (NE eq_refl) ].
Qed.

Lemma packages_complete {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) (pr : PackageRef s) :
  In pr (packages s).
Proof.
  unfold packages. apply in_flat_map. exists (pr_pos pr). split.
  - apply in_seq. pose proof (pr_lt pr); lia.
  - unfold mk_packageref. destruct (lt_dec (pr_pos pr) (package_count s)) as [H|H].
    + replace (package_at (pr_pos pr) H) with pr by (apply pkgref_positional; reflexivity). left; reflexivity.
    + exfalso; apply H; exact (pr_lt pr).
Qed.

Lemma one_surface_retained {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) :
  surf s = surf (package_surface idx).
Proof. unfold surf, package_surface; cbn [proj1_sig]. exact (proj2_sig s). Qed.

Definition packageref_eq_dec {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : {a = b} + {a <> b}.
Proof.
  destruct (Nat.eq_dec (pr_pos a) (pr_pos b)) as [E|NE].
  - left; apply pkgref_positional; exact E.
  - right; intro H; apply NE; rewrite H; reflexivity.
Defined.
Definition packageref_eqb {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : bool := if packageref_eq_dec a b then true else false.
Lemma packageref_eqb_spec {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx}
  (a b : PackageRef s) : packageref_eqb a b = true <-> a = b.
Proof. unfold packageref_eqb; destruct (packageref_eq_dec a b); split; congruence. Qed.

(* selected nonempty packages: those whose directory holds at least one nonempty file, in surface order *)
Definition is_selected {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx} (pr : PackageRef s) : bool :=
  existsb nonempty_file (pkg_members pr).
Definition selected_packages {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : list (PackageRef s) :=
  filter is_selected (packages s).

Inductive PackageSelection {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : Type :=
| NoSelected : PackageSelection s
| OneSelected : PackageRef s -> PackageSelection s
| MultipleSelected : PackageRef s -> PackageRef s -> list (PackageRef s) -> PackageSelection s.
Arguments NoSelected {p idx s}.
Arguments OneSelected {p idx s} _.
Arguments MultipleSelected {p idx s} _ _ _.

Definition package_selection {p} {idx : Index.Core.ProgramIndex p} (s : PackageSurface idx) : PackageSelection s :=
  match selected_packages s with
  | [] => NoSelected
  | a :: nil => OneSelected a
  | a :: b :: rest => MultipleSelected a b rest
  end.

(* the complete import path is module-path components ++ package-directory components *)
Local Open Scope string_scope.

Definition module_components {p} (idx : Index.Core.ProgramIndex p) : list string :=
  ModulePath.segments (Syntax.module_path (Syntax.module_spec p)).

Definition import_path {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx}
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
Definition default_exec_name {p} {idx : Index.Core.ProgramIndex p} {s : PackageSurface idx}
  (pr : PackageRef s) : string := default_exec_name_c (import_path pr).

(* the required executable-name helper cases: a terminal canonical vN (N>=2) strips, nothing else does *)
Example exec_m       : default_exec_name_c ["example.com"; "m"] = "m".               Proof. reflexivity. Qed.
Example exec_m_v2    : default_exec_name_c ["example.com"; "m"; "v2"] = "m".          Proof. reflexivity. Qed.
Example exec_m_a_v2  : default_exec_name_c ["example.com"; "m"; "a"; "v2"] = "a".     Proof. reflexivity. Qed.
Example exec_v2_root : default_exec_name_c ["example.com"; "v2"] = "example.com".     Proof. reflexivity. Qed.
Example exec_keep_v1     : default_exec_name_c ["m"; "v1"] = "v1".        Proof. reflexivity. Qed.
Example exec_keep_v01    : default_exec_name_c ["m"; "v01"] = "v01".      Proof. reflexivity. Qed.
Example exec_keep_verify : default_exec_name_c ["m"; "verify"] = "verify". Proof. reflexivity. Qed.
Example exec_keep_v2x    : default_exec_name_c ["m"; "v2x"] = "v2x".      Proof. reflexivity. Qed.
Example exec_nonterminal_v2 : default_exec_name_c ["m"; "v2"; "a"] = "a". Proof. reflexivity. Qed.

(* a module-root namespace entry is a subdirectory (its top component) or a root-level file (its stem) *)
Inductive RootEntryKind := RootDir | RootFile.
Definition rek_eq_dec (a b : RootEntryKind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* the root entry a source file contributes to: its top directory component, or its own stem at the root *)
Definition root_key {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx) : string * RootEntryKind :=
  match FilePath.pkg_components (FilePath.file_dir (Index.Core.fr_path fr)) with
  | c :: _ => (c, RootDir)
  | [] => (FilePath.strip_go (FilePath.text (Index.Core.fr_path fr)), RootFile)
  end.

Definition rootkey_eq_dec (a b : string * RootEntryKind) : {a = b} + {a <> b}.
Proof.
  destruct a as [a1 a2], b as [b1 b2].
  destruct (string_dec a1 b1) as [E1|N1]; [| right; congruence].
  destruct (rek_eq_dec a2 b2) as [E2|N2]; [ left; congruence | right; congruence ].
Defined.
Definition rootkey_eqb (a b : string * RootEntryKind) : bool := if rootkey_eq_dec a b then true else false.

Definition root_keys {p} (idx : Index.Core.ProgramIndex p) : list (string * RootEntryKind) :=
  nodup rootkey_eq_dec (map (@root_key p idx) (Index.Edges.all_files idx)).

(* the retained root entry: a position selector into the distinct root keys, carrying name, kind, contributors *)
Record RootEntryRef {p} (idx : Index.Core.ProgramIndex p) : Type := root_at {
  rr_pos : nat ;
  rr_lt  : rr_pos < length (root_keys idx)
}.
Arguments root_at {p idx} _ _.
Arguments rr_pos {p idx} _.
Arguments rr_lt {p idx} _.

Definition re_key {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : string * RootEntryKind :=
  Index.Model.nth_lt (root_keys idx) (rr_pos rr) (rr_lt rr).
Definition re_name {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : string := fst (re_key rr).
Definition re_kind {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : RootEntryKind := snd (re_key rr).
Definition re_files {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : list (Index.Core.FileRef idx) :=
  filter (fun fr => rootkey_eqb (root_key fr) (re_key rr)) (Index.Edges.all_files idx).

Definition mk_rootref {p} {idx : Index.Core.ProgramIndex p} (n : nat) : option (RootEntryRef idx) :=
  match lt_dec n (length (root_keys idx)) with left H => Some (root_at n H) | right _ => None end.
Definition root_entries {p} (idx : Index.Core.ProgramIndex p) : list (RootEntryRef idx) :=
  flat_map (fun n => match mk_rootref n with Some rr => [rr] | None => [] end) (seq 0 (length (root_keys idx))).

Lemma rr_positional {p} {idx : Index.Core.ProgramIndex p} (a b : RootEntryRef idx) :
  rr_pos a = rr_pos b -> a = b.
Proof. destruct a as [pa Ha], b as [pb Hb]; cbn; intro E; subst pb; f_equal; apply Index.Model.lt_unique. Qed.

Lemma re_key_in {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : In (re_key rr) (root_keys idx).
Proof. unfold re_key. apply nth_lt_In. Qed.

(* each retained root entry keeps a nonempty exact set of the source files that contribute to it *)
Lemma re_files_nonempty {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : re_files rr <> [].
Proof.
  pose proof (re_key_in rr) as Hin. unfold root_keys in Hin. rewrite nodup_In in Hin.
  apply in_map_iff in Hin. destruct Hin as [fr [Hk Hfr]].
  intro Hnil. assert (Hmem : In fr (re_files rr)).
  { unfold re_files. apply filter_In. split; [ exact Hfr | ].
    unfold rootkey_eqb. rewrite Hk. destruct (rootkey_eq_dec (re_key rr) (re_key rr)); [ reflexivity | congruence ]. }
  rewrite Hnil in Hmem. exact Hmem.
Qed.

(* the contributing files are exactly the source files whose root key is this entry's key *)
Lemma re_files_exact {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) (fr : Index.Core.FileRef idx) :
  In fr (re_files rr) <-> In fr (Index.Edges.all_files idx) /\ root_key fr = re_key rr.
Proof.
  unfold re_files. rewrite filter_In. unfold rootkey_eqb.
  split; intros [H1 H2]; (split; [ exact H1 | ]).
  - destruct (rootkey_eq_dec (root_key fr) (re_key rr)); [ assumption | discriminate ].
  - rewrite H2. destruct (rootkey_eq_dec (re_key rr) (re_key rr)); [ reflexivity | congruence ].
Qed.

Lemma root_entries_complete {p} {idx : Index.Core.ProgramIndex p} (rr : RootEntryRef idx) : In rr (root_entries idx).
Proof.
  unfold root_entries. apply in_flat_map. exists (rr_pos rr). split.
  - apply in_seq. pose proof (rr_lt rr); lia.
  - unfold mk_rootref. destruct (lt_dec (rr_pos rr) (length (root_keys idx))) as [H|H].
    + replace (root_at (rr_pos rr) H) with rr by (apply rr_positional; reflexivity). left; reflexivity.
    + exfalso; apply H; exact (rr_lt rr).
Qed.

Local Close Scope string_scope.
