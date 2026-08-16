(* Report — projection only.  It classifies nothing: it enumerates sites, reads the retained FactPhase and
   PackageFacts, and projects ordered diagnostics and boundaries. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec.
From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Packages Compilable.Facts.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module PK := Compilable.Packages.
Module FA := Compilable.Facts.

Inductive DiagSite {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| AtNode : Index.NodeRef idx -> DiagSite s
| AtPackage : PI.PackageRef s -> DiagSite s.
Arguments AtNode {p idx s} _.
Arguments AtPackage {p idx s} _.

Inductive ReportRoot {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| RootNode : Index.NodeRef idx -> ReportRoot s
| RootPackage : PI.PackageRef s -> ReportRoot s
| RootSelf : ReportRoot s.
Arguments RootNode {p idx s} _.
Arguments RootPackage {p idx s} _.
Arguments RootSelf {p idx s}.

Inductive ReportCause {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| OccCause : FA.Cause idx -> ReportCause s
| PkgMissingMain : PI.PackageRef s -> ReportCause s
| PkgMainRedeclared : forall pr : PI.PackageRef s,
    BN.MainDeclRef s pr -> BN.MainDeclRef s pr -> list (BN.MainDeclRef s pr) -> ReportCause s
| PkgOutputCollision : PI.PackageRef s -> ReportCause s.
Arguments OccCause {p idx s} _.
Arguments PkgMissingMain {p idx s} _.
Arguments PkgMainRedeclared {p idx s} _ _ _ _.
Arguments PkgOutputCollision {p idx s} _.

Section OverPhases.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FA.FactPhase bp) (pf : PK.PackageFacts bp).

(* ---- outcome inspectors ---- *)

Definition v_invalid {r : Index.NodeRef idx} (o : FA.ValueOutcome r) : bool := match o with FA.VInvalid _ => true | _ => false end.
Definition a_invalid {r : Index.NodeRef idx} (o : FA.AppOutcome r) : bool := match o with FA.AInvalid _ => true | _ => false end.
Definition s_invalid {r : Index.NodeRef idx} (o : FA.StmtOutcome r) : bool := match o with FA.SInvalid _ => true | _ => false end.
Definition t_invalid {r : Index.NodeRef idx} (o : FA.TypeUseOutcome r) : bool := match o with FA.TInvalid _ => true | _ => false end.
Definition v_unmet {r : Index.NodeRef idx} (o : FA.ValueOutcome r) : bool := match o with FA.VUnmet _ => true | _ => false end.
Definition a_unmet {r : Index.NodeRef idx} (o : FA.AppOutcome r) : bool := match o with FA.AUnmet _ => true | _ => false end.
Definition s_unmet {r : Index.NodeRef idx} (o : FA.StmtOutcome r) : bool := match o with FA.SUnmet _ => true | _ => false end.
Definition t_unmet {r : Index.NodeRef idx} (o : FA.TypeUseOutcome r) : bool := match o with FA.TUnmet _ => true | _ => false end.

Definition node_diag (r : Index.NodeRef idx) : bool :=
  v_invalid (FA.value_fact fp r) || a_invalid (FA.app_fact fp r)
  || s_invalid (FA.stmt_fact fp r) || t_invalid (FA.type_use_fact fp r).
Definition node_bound (r : Index.NodeRef idx) : bool :=
  negb (node_diag r) &&
  (v_unmet (FA.value_fact fp r) || a_unmet (FA.app_fact fp r)
   || s_unmet (FA.stmt_fact fp r) || t_unmet (FA.type_use_fact fp r)).

(* ---- package-level facts ---- *)

Definition pkg_main_issue (pr : PI.PackageRef s) : bool :=
  match BN.package_main bp pr with BN.MainMissing => true | BN.MainRedeclared _ _ _ => true | _ => false end.
Definition collision_list : list (PI.PackageRef s) :=
  match PK.preflight pf with PK.FreshOk => [] | PK.FreshCollisions first rest => first :: rest end.
Definition pkg_collides (pr : PI.PackageRef s) : bool := existsb (PI.packageref_eqb pr) collision_list.

Definition produces_diag (site : DiagSite s) : bool :=
  match site with
  | AtNode r => node_diag r
  | AtPackage pr => pkg_main_issue pr || pkg_collides pr
  end.
Definition produces_bound (site : DiagSite s) : bool :=
  let _ := pf in match site with AtNode r => node_bound r | AtPackage _ => false end.

Record Diagnostic := diag_at { diag_site : DiagSite s ; diag_ok : produces_diag diag_site = true }.
Record Boundary := bound_at { bound_site : Index.NodeRef idx ; bound_ok : produces_bound (AtNode bound_site) = true }.

(* ---- cause / related / root projections ---- *)

Definition occ_cause_of (r : Index.NodeRef idx) : FA.Cause idx :=
  match FA.value_fact fp r with
  | FA.VInvalid c => c
  | _ => match FA.app_fact fp r with
         | FA.AInvalid c => c
         | _ => match FA.stmt_fact fp r with
                | FA.SInvalid c => c
                | _ => match FA.type_use_fact fp r with FA.TInvalid c => c | _ => FA.IllegalStatement end
                end
         end
  end.

Definition diag_cause (d : Diagnostic) : ReportCause s :=
  match diag_site d with
  | AtNode r => OccCause (occ_cause_of r)
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainMissing => PkgMissingMain pr
      | BN.MainRedeclared m1 m2 rest => PkgMainRedeclared pr m1 m2 rest
      | BN.MainUnique _ => PkgOutputCollision pr
      end
  end.

Definition occ_related (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  match FA.value_fact fp r with
  | FA.VInvalid (FA.ComplexMismatch a b) => [a; b]
  | _ => []
  end.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) :=
  match diag_site d with
  | AtNode r => occ_related r
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainRedeclared m1 m2 rest => map BN.main_node (m1 :: m2 :: rest)
      | _ => []
      end
  end.
Definition diag_root (d : Diagnostic) : ReportRoot s :=
  match diag_site d with AtNode r => RootNode r | AtPackage pr => RootPackage pr end.

Definition bound_req (b : Boundary) : FA.Requirement idx :=
  let r := bound_site b in
  match FA.value_fact fp r with
  | FA.VUnmet q => q
  | _ => match FA.app_fact fp r with
         | FA.AUnmet q => q
         | _ => match FA.stmt_fact fp r with
                | FA.SUnmet q => q
                | _ => match FA.type_use_fact fp r with FA.TUnmet q => q | _ => FA.ReqComplexType r end
                end
         end
  end.
Definition bound_root (b : Boundary) : ReportRoot s := RootNode (bound_site b).

(* ---- enumeration ---- *)

Definition all_nodes : list (Index.NodeRef idx) :=
  flat_map Index.file_nodes (flat_map PI.pkg_members (PI.packages s)).

Fixpoint build_diags (sites : list (DiagSite s))
  : (forall d, In d sites -> produces_diag d = true) -> list Diagnostic :=
  match sites with
  | [] => fun _ => []
  | site :: rest => fun H =>
      diag_at site (H site (or_introl eq_refl)) :: build_diags rest (fun d Hd => H d (or_intror Hd))
  end.
Fixpoint build_bounds (nodes : list (Index.NodeRef idx))
  : (forall r, In r nodes -> produces_bound (AtNode r) = true) -> list Boundary :=
  match nodes with
  | [] => fun _ => []
  | r :: rest => fun H =>
      bound_at r (H r (or_introl eq_refl)) :: build_bounds rest (fun r' Hr' => H r' (or_intror Hr'))
  end.

Lemma filter_diag_ok : forall (sites : list (DiagSite s)) d,
  In d (filter produces_diag sites) -> produces_diag d = true.
Proof. intros sites d Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.
Lemma filter_bound_ok : forall (nodes : list (Index.NodeRef idx)) r,
  In r (filter (fun r0 => produces_bound (AtNode r0)) nodes) -> produces_bound (AtNode r) = true.
Proof. intros nodes r Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.

Definition collision_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage collision_list)) (filter_diag_ok _).
Definition main_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage (filter pkg_main_issue (PI.packages s))))
              (filter_diag_ok _).
Definition occ_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtNode all_nodes)) (filter_diag_ok _).

Definition diagnostics : list Diagnostic := collision_diags ++ main_diags ++ occ_diags.
Definition boundaries : list Boundary :=
  build_bounds (filter (fun r => produces_bound (AtNode r)) all_nodes) (filter_bound_ok _).

End OverPhases.

(* ---- laws ---- *)

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FA.FactPhase bp) (pf : PK.PackageFacts bp).

(* a diagnostic stores only its site plus a producing proof; the proof is irrelevant *)
Lemma report_projection_only (d1 d2 : Diagnostic fp pf) :
  diag_site fp pf d1 = diag_site fp pf d2 -> d1 = d2.
Proof. destruct d1 as [a Ha], d2 as [b Hb]; cbn; intro E; subst b; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* cause is a projection of the site and retained phases, not stored *)
Lemma diag_cause_from_phase (d1 d2 : Diagnostic fp pf) :
  diag_site fp pf d1 = diag_site fp pf d2 -> diag_cause fp pf d1 = diag_cause fp pf d2.
Proof. intro E; unfold diag_cause; rewrite E; reflexivity. Qed.

(* a main-redeclaration package diagnostic projects the exact retained references and related nodes *)
Lemma main_redeclared_related_exact (d : Diagnostic fp pf) (pr : PI.PackageRef s)
      (m1 m2 : BN.MainDeclRef s pr) (rest : list (BN.MainDeclRef s pr)) :
  diag_site fp pf d = AtPackage pr ->
  BN.package_main bp pr = BN.MainRedeclared m1 m2 rest ->
  diag_cause fp pf d = PkgMainRedeclared pr m1 m2 rest
  /\ diag_related fp pf d = map BN.main_node (m1 :: m2 :: rest)
  /\ diag_root fp pf d = RootPackage pr.
Proof.
  intros Hsite Hpm. unfold diag_cause, diag_related, diag_root; rewrite Hsite, Hpm.
  repeat split; reflexivity.
Qed.

(* the root algebra is total *)
Lemma root_algebra_total (d : Diagnostic fp pf) :
  (exists r, diag_root fp pf d = RootNode r) \/ (exists pr, diag_root fp pf d = RootPackage pr).
Proof. unfold diag_root; destruct (diag_site fp pf d); eauto. Qed.

(* the diagnostic order is preflight, then package, then occurrence *)
Lemma precedence_total :
  diagnostics fp pf = collision_diags fp pf ++ main_diags fp pf ++ occ_diags fp pf.
Proof. reflexivity. Qed.

(* a blocked node produces no diagnostic and no boundary of its own *)
Lemma no_duplicate_blocked (r : Index.NodeRef idx) (w : FA.BlockWitness r) :
  FA.find_failing bp r = Some w -> produces_diag fp pf (AtNode r) = false /\ produces_bound fp pf (AtNode r) = false.
Proof.
  intro H.
  destruct (FA.outcome_site_retained bp fp r) as [Rv [Ra [Rs Rt]]].
  assert (Ev : FA.value_fact fp r = FA.VBlocked w) by (rewrite Rv; unfold FA.value_fact_c; rewrite H; reflexivity).
  assert (Ea : FA.app_fact fp r = FA.ABlocked w) by (rewrite Ra; unfold FA.app_fact_c; rewrite H; reflexivity).
  assert (Es : FA.stmt_fact fp r = FA.SBlocked w) by (rewrite Rs; unfold FA.stmt_fact_c; rewrite H; reflexivity).
  assert (Et : FA.type_use_fact fp r = FA.TBlocked w) by (rewrite Rt; unfold FA.type_fact_c; rewrite H; reflexivity).
  split.
  - change (node_diag fp r = false); unfold node_diag.
    rewrite Ev, Ea, Es, Et; reflexivity.
  - change (node_bound fp r = false); unfold node_bound, node_diag.
    rewrite Ev, Ea, Es, Et; reflexivity.
Qed.

(* a site that produces a diagnostic produces no boundary *)
Lemma decided_invalid_no_boundary (site : DiagSite s) :
  produces_diag fp pf site = true -> produces_bound fp pf site = false.
Proof.
  destruct site as [r|pr]; cbn.
  - unfold node_bound; intro H; rewrite H; reflexivity.
  - intros _; reflexivity.
Qed.

End Laws.
