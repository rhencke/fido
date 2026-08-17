(* Report — projection only: folds the retained facts stream into ordered diagnostics and boundaries, no lookup. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec.
From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Packages Compilable.Facts.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module PK := Compilable.Packages.
Module FA := Compilable.Facts.

Inductive DiagSite {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| AtOcc : FA.NodeFacts idx -> DiagSite s
| AtPackage : PI.PackageRef s -> DiagSite s.
Arguments AtOcc {p idx s} _.
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

(* outcome inspectors: read a single retained outcome in place, no index transport *)
Definition v_invalid {r : Index.NodeRef idx} (o : FA.ValueOutcome r) : bool := match o with FA.VInvalid _ => true | _ => false end.
Definition a_invalid {r : Index.NodeRef idx} (o : FA.AppOutcome r) : bool := match o with FA.AInvalid _ => true | _ => false end.
Definition s_invalid {r : Index.NodeRef idx} (o : FA.StmtOutcome r) : bool := match o with FA.SInvalid _ => true | _ => false end.
Definition t_invalid {r : Index.NodeRef idx} (o : FA.TypeUseOutcome r) : bool := match o with FA.TInvalid _ => true | _ => false end.
Definition v_unmet {r : Index.NodeRef idx} (o : FA.ValueOutcome r) : bool := match o with FA.VUnmet _ => true | _ => false end.
Definition a_unmet {r : Index.NodeRef idx} (o : FA.AppOutcome r) : bool := match o with FA.AUnmet _ => true | _ => false end.
Definition s_unmet {r : Index.NodeRef idx} (o : FA.StmtOutcome r) : bool := match o with FA.SUnmet _ => true | _ => false end.
Definition t_unmet {r : Index.NodeRef idx} (o : FA.TypeUseOutcome r) : bool := match o with FA.TUnmet _ => true | _ => false end.

(* per-node predicates, read directly from the retained NodeFacts: no per-query lookup *)
Definition facts_diag (nf : FA.NodeFacts idx) : bool :=
  v_invalid (FA.nf_v nf) || a_invalid (FA.nf_a nf) || s_invalid (FA.nf_s nf) || t_invalid (FA.nf_t nf).
Definition facts_bound (nf : FA.NodeFacts idx) : bool :=
  negb (facts_diag nf) &&
  (v_unmet (FA.nf_v nf) || a_unmet (FA.nf_a nf) || s_unmet (FA.nf_s nf) || t_unmet (FA.nf_t nf)).

Definition pkg_main_issue (pr : PI.PackageRef s) : bool :=
  match BN.package_main bp pr with BN.MainMissing => true | BN.MainRedeclared _ _ _ => true | _ => false end.
Definition collision_list : list (PI.PackageRef s) :=
  match PK.preflight pf with PK.FreshOk => [] | PK.FreshCollisions first rest => first :: rest end.
Definition pkg_collides (pr : PI.PackageRef s) : bool := existsb (PI.packageref_eqb pr) collision_list.

(* the diagnostic-producing test of a site; an occurrence carries its own retained facts, read in place *)
Definition produces_diag (site : DiagSite s) : bool :=
  let _ := fp in
  match site with
  | AtOcc nf => facts_diag nf
  | AtPackage pr => pkg_main_issue pr || pkg_collides pr
  end.
Definition produces_bound (nf : FA.NodeFacts idx) : bool := let _ := fp in let _ := pf in facts_bound nf.

Record Diagnostic := diag_at { diag_site : DiagSite s ; diag_ok : produces_diag diag_site = true }.
Record Boundary := bound_at { bound_facts : FA.NodeFacts idx ; bound_ok : produces_bound bound_facts = true }.

(* cause / related / root projections, all read from the retained NodeFacts *)
Definition facts_cause (nf : FA.NodeFacts idx) : FA.Cause idx :=
  match FA.nf_v nf with
  | FA.VInvalid c => c
  | _ => match FA.nf_a nf with
         | FA.AInvalid c => c
         | _ => match FA.nf_s nf with
                | FA.SInvalid c => c
                | _ => match FA.nf_t nf with FA.TInvalid c => c | _ => FA.IllegalStatement end
                end
         end
  end.
Definition diag_cause (d : Diagnostic) : ReportCause s :=
  match diag_site d with
  | AtOcc nf => OccCause (facts_cause nf)
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainMissing => PkgMissingMain pr
      | BN.MainRedeclared m1 m2 rest => PkgMainRedeclared pr m1 m2 rest
      | BN.MainUnique _ => PkgOutputCollision pr
      end
  end.

Definition facts_related (nf : FA.NodeFacts idx) : list (Index.NodeRef idx) :=
  match FA.nf_v nf with FA.VInvalid (FA.ComplexMismatch a b) => [a; b] | _ => [] end.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) :=
  match diag_site d with
  | AtOcc nf => facts_related nf
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainRedeclared m1 m2 rest => map BN.main_node (m1 :: m2 :: rest)
      | _ => []
      end
  end.
Definition diag_root (d : Diagnostic) : ReportRoot s :=
  match diag_site d with AtOcc nf => RootNode (FA.nf_node nf) | AtPackage pr => RootPackage pr end.

Definition facts_req (nf : FA.NodeFacts idx) : FA.Requirement idx :=
  match FA.nf_v nf with
  | FA.VUnmet q => q
  | _ => match FA.nf_a nf with
         | FA.AUnmet q => q
         | _ => match FA.nf_s nf with
                | FA.SUnmet q => q
                | _ => match FA.nf_t nf with FA.TUnmet q => q | _ => FA.ReqComplexType (FA.nf_node nf) end
                end
         end
  end.
Definition bound_req (b : Boundary) : FA.Requirement idx := facts_req (bound_facts b).
Definition bound_root (b : Boundary) : ReportRoot s := RootNode (FA.nf_node (bound_facts b)).

(* enumeration: fold the retained stream directly, no all_nodes reconstruction, no lookup4 *)
Fixpoint build_diags (sites : list (DiagSite s))
  : (forall d, In d sites -> produces_diag d = true) -> list Diagnostic :=
  match sites with
  | [] => fun _ => []
  | site :: rest => fun H =>
      diag_at site (H site (or_introl eq_refl)) :: build_diags rest (fun d Hd => H d (or_intror Hd))
  end.
Fixpoint build_bounds (nfs : list (FA.NodeFacts idx))
  : (forall nf, In nf nfs -> produces_bound nf = true) -> list Boundary :=
  match nfs with
  | [] => fun _ => []
  | nf :: rest => fun H =>
      bound_at nf (H nf (or_introl eq_refl)) :: build_bounds rest (fun nf' Hnf' => H nf' (or_intror Hnf'))
  end.

Lemma filter_diag_ok : forall (sites : list (DiagSite s)) d,
  In d (filter produces_diag sites) -> produces_diag d = true.
Proof. intros sites d Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.
Lemma filter_bound_ok : forall (nfs : list (FA.NodeFacts idx)) nf,
  In nf (filter produces_bound nfs) -> produces_bound nf = true.
Proof. intros nfs nf Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.

Definition collision_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage collision_list)) (filter_diag_ok _).
Definition main_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage (filter pkg_main_issue (PI.packages s))))
              (filter_diag_ok _).
Definition occ_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtOcc (FA.fact_list fp))) (filter_diag_ok _).

Definition diagnostics : list Diagnostic := collision_diags ++ main_diags ++ occ_diags.
Definition boundaries : list Boundary :=
  build_bounds (filter produces_bound (FA.fact_list fp)) (filter_bound_ok _).

End OverPhases.

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

(* a blocked node's facts are all Blocked, so folding the stream emits neither diagnostic nor boundary for it *)
Lemma no_duplicate_blocked (r : Index.NodeRef idx) (w : FA.BlockWitness r) :
  FA.find_failing bp r = Some w ->
  produces_diag fp pf (AtOcc (FA.build_nf bp (FA.dfails bp) r)) = false
  /\ produces_bound fp pf (FA.build_nf bp (FA.dfails bp) r) = false.
Proof. intro H. rewrite (FA.build_nf_blocked bp r w H). split; reflexivity. Qed.

(* a node that produces a diagnostic produces no boundary (the boundary gate negates the diagnostic bit) *)
Lemma decided_invalid_no_boundary (nf : FA.NodeFacts idx) :
  facts_diag nf = true -> produces_bound fp pf nf = false.
Proof. unfold produces_bound, facts_bound; intro H; rewrite H; reflexivity. Qed.

End Laws.
