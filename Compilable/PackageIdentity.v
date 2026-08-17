From Stdlib Require Import List Bool Arith PeanoNat Lia String.
From Fido Require Import Syntax Index FilePath.
Import ListNotations.
Local Open Scope string_scope.

(* Package identity is the exact PackageRef over the retained package-dir surface, never a raw string. *)

Definition surface_dirs {p} (idx : Index.ProgramIndex p) : list FilePath.PkgDir :=
  nodup FilePath.pkgdir_eq_dec (map (fun e => FilePath.file_dir (fst e)) (Index.prog_occs idx)).

(* PackageSurface is pinned to the canonical surface, so every surface is that surface and reduces to its dir list. *)
Definition PackageSurface {p} (idx : Index.ProgramIndex p) : Type :=
  { l : list FilePath.PkgDir | l = surface_dirs idx }.

Definition package_surface {p} (idx : Index.ProgramIndex p) : PackageSurface idx :=
  exist _ (surface_dirs idx) eq_refl.

Definition surf {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : list FilePath.PkgDir := proj1_sig s.

Definition package_count {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : nat := Datatypes.length (surf s).

Record PackageRef {p} {idx : Index.ProgramIndex p} (s : PackageSurface idx) : Type := package_at {
  pr_pos : nat ;
  pr_lt  : pr_pos < package_count s
}.
Arguments package_at {p idx s} _ _.
Arguments pr_pos {p idx s} _.
Arguments pr_lt {p idx s} _.

Definition pkg_dir {p} {idx : Index.ProgramIndex p}{s : PackageSurface idx} (pr : PackageRef s) : FilePath.PkgDir :=
  Index.nth_lt (surf s) (pr_pos pr) (pr_lt pr).

Definition pkg_text {p} {idx : Index.ProgramIndex p}{s : PackageSurface idx} (pr : PackageRef s) : String.string :=
  String.concat "/" (FilePath.pkg_components (pkg_dir pr)).

Definition member_refs {p} (idx : Index.ProgramIndex p) (target : FilePath.PkgDir)
                       (l : list (FilePath.T * list Index.Occ)) : list (Index.FileRef idx) :=
  fold_right (fun e acc =>
    match Index.mk_fileref idx (fst e) with
    | Some fr => if FilePath.pkgdir_eq_dec (FilePath.file_dir (fst e)) target then fr :: acc else acc
    | None => acc
    end) [] l.

Definition pkg_members {p} {idx : Index.ProgramIndex p}{s : PackageSurface idx} (pr : PackageRef s) : list (Index.FileRef idx) :=
  member_refs idx (pkg_dir pr) (Index.prog_occs idx).

Lemma member_refs_spec {p} (idx : Index.ProgramIndex p) (target : FilePath.PkgDir) :
  forall l fr, In fr (member_refs idx target l)
    <-> (exists e, In e l /\ Index.mk_fileref idx (fst e) = Some fr /\ FilePath.file_dir (fst e) = target).
Proof.
  induction l as [|e l IH]; intro fr; cbn [member_refs fold_right].
  - split; [ intros [] | intros [e0 [[] _]] ].
  - destruct (Index.mk_fileref idx (fst e)) as [fr0|] eqn:Emk.
    + destruct (FilePath.pkgdir_eq_dec (FilePath.file_dir (fst e)) target) as [Ed|Ed].
      * split.
        -- intros [->|Hin].
           ++ exists e; split; [ left; reflexivity | split; [ exact Emk | exact Ed ] ].
           ++ apply IH in Hin. destruct Hin as [e0 [Hin0 [Hmk0 Hd0]]].
              exists e0; split; [ right; exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
        -- intros [e0 [[He0|Hin0] [Hmk0 Hd0]]].
           ++ subst e0. rewrite Emk in Hmk0. injection Hmk0 as ->. left; reflexivity.
           ++ right. apply IH. exists e0; split; [ exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
      * rewrite IH. split.
        -- intros [e0 [Hin0 [Hmk0 Hd0]]]. exists e0; split; [ right; exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
        -- intros [e0 [[He0|Hin0] [Hmk0 Hd0]]].
           ++ subst e0. rewrite Hd0 in Ed. contradiction Ed; reflexivity.
           ++ exists e0; split; [ exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
    + rewrite IH. split.
      * intros [e0 [Hin0 [Hmk0 Hd0]]]. exists e0; split; [ right; exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
      * intros [e0 [[He0|Hin0] [Hmk0 Hd0]]].
        -- subst e0. rewrite Emk in Hmk0. discriminate Hmk0.
        -- exists e0; split; [ exact Hin0 | split; [ exact Hmk0 | exact Hd0 ] ].
Qed.

Lemma file_dir_in_surface {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) :
  In (FilePath.file_dir (Index.fr_path fr)) (surface_dirs idx).
Proof.
  unfold surface_dirs. rewrite nodup_In.
  destruct (Index.index_has_file_in idx (Index.fr_path fr) (Index.fr_in fr)) as [e [Hin He]].
  apply in_map_iff. exists e; split; [ rewrite He; reflexivity | exact Hin ].
Qed.

Fixpoint first_index (d : FilePath.PkgDir) (l : list FilePath.PkgDir) : nat :=
  match l with
  | [] => 0
  | x :: xs => if FilePath.pkgdir_eq_dec x d then 0 else S (first_index d xs)
  end.

Lemma first_index_lt : forall d l, In d l -> first_index d l < Datatypes.length l.
Proof.
  induction l as [|x xs IH]; intro Hin; cbn [first_index Datatypes.length].
  - destruct Hin.
  - destruct (FilePath.pkgdir_eq_dec x d) as [E|NE].
    + lia.
    + destruct Hin as [Heq|Hin]; [ contradiction (NE Heq) |]. specialize (IH Hin); lia.
Qed.

Lemma first_index_nth : forall d l, In d l -> nth_error l (first_index d l) = Some d.
Proof.
  induction l as [|x xs IH]; intro Hin; cbn [first_index].
  - destruct Hin.
  - destruct (FilePath.pkgdir_eq_dec x d) as [E|NE].
    + cbn [nth_error]; rewrite E; reflexivity.
    + destruct Hin as [Heq|Hin]; [ contradiction (NE Heq) |]. cbn [nth_error]. apply IH; exact Hin.
Qed.

Lemma pof_lt {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) (fr : Index.FileRef idx) :
  first_index (FilePath.file_dir (Index.fr_path fr)) (surf s) < package_count s.
Proof.
  unfold package_count. apply first_index_lt.
  unfold surf; rewrite (proj2_sig s). apply file_dir_in_surface.
Qed.

Definition package_of_file {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) (fr : Index.FileRef idx) : PackageRef s :=
  package_at (first_index (FilePath.file_dir (Index.fr_path fr)) (surf s)) (pof_lt s fr).

Definition mk_packageref {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) (n : nat) : option (PackageRef s) :=
  match lt_dec n (package_count s) with left H => Some (package_at n H) | right _ => None end.

Definition packages {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) : list (PackageRef s) :=
  flat_map (fun n => match mk_packageref s n with Some pr => [pr] | None => [] end) (seq 0 (package_count s)).

Lemma pkgref_positional {p} {idx : Index.ProgramIndex p}{s : PackageSurface idx} (a b : PackageRef s) :
  pr_pos a = pr_pos b -> a = b.
Proof. destruct a as [pa Ha], b as [pb Hb]; cbn; intro E; subst pb; f_equal; apply Index.lt_unique. Qed.

Lemma pkg_members_exact {p} {idx : Index.ProgramIndex p}{s : PackageSurface idx} (pr : PackageRef s) (fr : Index.FileRef idx) :
  In fr (pkg_members pr) <-> FilePath.file_dir (Index.fr_path fr) = pkg_dir pr.
Proof.
  unfold pkg_members. rewrite member_refs_spec. split.
  - intros [e [Hin [Hmk Hd]]]. apply Index.mk_fileref_path in Hmk. rewrite <- Hmk in Hd. exact Hd.
  - intro Hd. destruct (Index.index_has_file_in idx (Index.fr_path fr) (Index.fr_in fr)) as [e [Hin He]].
    assert (Hhf : Index.index_has_file idx (fst e) = true) by (apply Index.in_index_has_file; exact Hin).
    destruct (Index.mk_fileref_of_in idx (fst e) Hhf) as [fr' [Hmk Hp]].
    assert (fr' = fr) by (apply Index.fileref_positional; rewrite Hp; exact He).
    subst fr'. exists e; split; [ exact Hin | split; [ exact Hmk | rewrite He; exact Hd ] ].
Qed.

Lemma package_of_file_total {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) (fr : Index.FileRef idx) :
  pkg_dir (package_of_file s fr) = FilePath.file_dir (Index.fr_path fr).
Proof.
  unfold pkg_dir, package_of_file; cbn [pr_pos pr_lt].
  set (d := FilePath.file_dir (Index.fr_path fr)).
  assert (Hin : In d (surf s)) by (unfold d, surf; rewrite (proj2_sig s); apply file_dir_in_surface).
  pose proof (Index.nth_lt_nth_error (surf s) (first_index d (surf s)) (pof_lt s fr)) as E1.
  rewrite (first_index_nth d (surf s) Hin) in E1. injection E1 as E1. symmetry; exact E1.
Qed.

Lemma packages_complete {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) (pr : PackageRef s) : In pr (packages s).
Proof.
  unfold packages. apply in_flat_map. exists (pr_pos pr). split.
  - apply in_seq. pose proof (pr_lt pr); lia.
  - unfold mk_packageref. destruct (lt_dec (pr_pos pr) (package_count s)) as [H|H].
    + replace (package_at (pr_pos pr) H) with pr by (apply pkgref_positional; reflexivity).
      left; reflexivity.
    + exfalso; apply H; exact (pr_lt pr).
Qed.

Lemma pkg_dir_injective_in_surface {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
      (a b : PackageRef s) :
  pkg_dir a = pkg_dir b -> a = b.
Proof.
  intro Hd. apply pkgref_positional.
  assert (Hnd : NoDup (surf s))
    by (unfold surf; rewrite (proj2_sig s); unfold surface_dirs; apply NoDup_nodup).
  assert (Enth : nth_error (surf s) (pr_pos a) = nth_error (surf s) (pr_pos b)).
  { rewrite (Index.nth_lt_nth_error _ (pr_pos a) (pr_lt a)),
            (Index.nth_lt_nth_error _ (pr_pos b) (pr_lt b)).
    f_equal. exact Hd. }
  exact (proj1 (NoDup_nth_error _) Hnd (pr_pos a) (pr_pos b) (pr_lt a) Enth).
Qed.

Lemma one_surface_retained {p} {idx : Index.ProgramIndex p}(s : PackageSurface idx) : surf s = surf (package_surface idx).
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

(* a file's own package is the one whose members contain it *)
Lemma package_of_file_member {p} {idx : Index.ProgramIndex p} {s : PackageSurface idx}
  (pr : PackageRef s) (fr : Index.FileRef idx) :
  In fr (pkg_members pr) -> package_of_file s fr = pr.
Proof.
  intro Hin. apply pkg_members_exact in Hin.
  apply pkg_dir_injective_in_surface. rewrite (package_of_file_total s fr). exact Hin.
Qed.
