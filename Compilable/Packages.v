(* Packages — the fresh-build preflight, and the projected binding-owned package-main status. *)

From Stdlib Require Import List Bool String Ascii Arith PeanoNat Lia.
From Fido Require Import Syntax Index FilePath Compilable.PackageIdentity Compilable.Bindings.
Import ListNotations.
Local Open Scope string_scope.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.

(* cmd/go's default executable name: the last import-path component, dropping a trailing version element. *)

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

Inductive FreshBuildDisposition {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| FreshOk : FreshBuildDisposition s
| FreshCollisions : PI.PackageRef s -> list (PI.PackageRef s) -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollisions {p idx s} _ _.

(* a package's default executable output name, from its directory components alone *)
Definition exec_name_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : string := default_exec_name_c (FilePath.pkg_components (PI.pkg_dir pr)).

(* the top-level directory names present in the program: the first component of each package's directory *)
Definition first_dir_component {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : option string :=
  match FilePath.pkg_components (PI.pkg_dir pr) with c :: _ => Some c | [] => None end.
Definition root_dir_names {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : list string :=
  fold_right (fun pr acc => match first_dir_component pr with Some c => c :: acc | None => acc end) [] (PI.packages s).

Definition is_command_pkg {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) (pr : PI.PackageRef s) : bool :=
  match BN.package_main bp pr with BN.MainUnique _ => true | _ => false end.

(* a sole-main package collides when its default executable name is an existing root directory *)
Definition collides {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) (pr : PI.PackageRef s) : bool :=
  andb (is_command_pkg bp pr) (existsb (String.eqb (exec_name_of pr)) (root_dir_names s)).

Definition colliding_pkgs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : list (PI.PackageRef s) := filter (collides bp) (PI.packages s).

Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : FreshBuildDisposition s :=
  match colliding_pkgs bp with [] => FreshOk | first :: rest => FreshCollisions first rest end.

Definition PackageFacts {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : Type := { d : FreshBuildDisposition s | d = raw_preflight bp }.
Definition package_facts {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : PackageFacts bp := exist _ (raw_preflight bp) eq_refl.
Definition preflight {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
  (pf : PackageFacts bp) : FreshBuildDisposition s := proj1_sig pf.
Definition package_rule {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
  (pf : PackageFacts bp) (pr : PI.PackageRef s) : BN.MainStatus s pr := BN.package_main bp pr.

Lemma package_rule_is_projection {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {bp : BN.BindingPhase s} (pf : PackageFacts bp) (pr : PI.PackageRef s) :
  package_rule pf pr = BN.package_main bp pr.
Proof. reflexivity. Qed.

Lemma preflight_multiplicity_total {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {bp : BN.BindingPhase s} (pf : PackageFacts bp) :
  match preflight pf with
  | FreshOk => colliding_pkgs bp = []
  | FreshCollisions first rest => colliding_pkgs bp = first :: rest
  end.
Proof.
  unfold preflight. rewrite (proj2_sig pf). unfold raw_preflight.
  destruct (colliding_pkgs bp) as [|first rest]; reflexivity.
Qed.

Lemma packages_consume_one_surface {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {bp : BN.BindingPhase s} (pf : PackageFacts bp) : preflight pf = raw_preflight bp.
Proof. exact (proj2_sig pf). Qed.
