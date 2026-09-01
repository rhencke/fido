(* Report — the projection of the one canonical Analysis issue table into ordered diagnostics and boundaries. *)

From Stdlib Require Import List.
From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.

(* Report owns no cause, severity, order, or fallback: every member and its order is exactly the one Result's. *)
Section Project.
Context {p : Syntax.Program} (r : AN.Result p).

Definition Diagnostic : Type := AN.Diagnostic r.
Definition Boundary : Type := AN.Boundary r.
Definition result_diagnostics : list Diagnostic := AN.result_diagnostics r.
Definition result_boundaries : list Boundary := AN.result_boundaries r.

(* member projections: each reads the exact field the Analysis row already retains, never a reread or reconstruction *)
Definition diag_cause (d : Diagnostic) : AN.IssueCause r := AN.diag_cause d.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef (AN.res_index r)) := AN.diag_related d.
Definition diag_root (d : Diagnostic) : AN.IssueRoot r := AN.diag_root d.
Definition bound_req_ref (b : Boundary) : AN.UnmetFactRef r := AN.bound_req_ref b.
Definition bound_root (b : Boundary) : AN.IssueRoot r := AN.bound_root b.

(* exact projection: Report's diagnostics/boundaries ARE the Result's issue lists, same members and order, no repair *)
Lemma result_diagnostics_exact : result_diagnostics = AN.result_diagnostics r.
Proof. reflexivity. Qed.
Lemma result_boundaries_exact : result_boundaries = AN.result_boundaries r.
Proof. reflexivity. Qed.
Lemma diag_cause_exact : forall d, diag_cause d = AN.diag_cause d.
Proof. reflexivity. Qed.
Lemma diag_related_exact : forall d, diag_related d = AN.diag_related d.
Proof. reflexivity. Qed.
Lemma diag_root_exact : forall d, diag_root d = AN.diag_root d.
Proof. reflexivity. Qed.
Lemma bound_req_ref_exact : forall b, bound_req_ref b = AN.bound_req_ref b.
Proof. reflexivity. Qed.
Lemma bound_root_exact : forall b, bound_root b = AN.bound_root b.
Proof. reflexivity. Qed.

End Project.

Arguments Diagnostic {p} r.
Arguments Boundary {p} r.
Arguments diag_cause {p r} d. Arguments diag_related {p r} d. Arguments diag_root {p r} d.
Arguments bound_req_ref {p r} b. Arguments bound_root {p r} b.

(* Report projects the exact ordinal-indexed issue identities of the one retained result, and nothing more. *)
Section IssueReport.
Context {p : Syntax.Program}.

Definition Issue (r : AN.Result p) : Type := AN.Issue r.
Definition IssueRef (r : AN.Result p) : Type := AN.IssueRef r.
Definition result_issues (r : AN.Result p) : list (AN.Issue r) := AN.result_issues r.
Definition ir_ord {r : AN.Result p} (ref : AN.IssueRef r) : nat := AN.ir_ord ref.
Definition ir_row {r : AN.Result p} (ref : AN.IssueRef r) : AN.Issue r := AN.ir_row ref.

(* the exact class, root, family, cause-or-requirement, and per-class row an issue projects *)
Definition issue_class {r : AN.Result p} (i : AN.Issue r) : AN.IssueClass := AN.issue_class i.
Definition issue_root {r : AN.Result p} (i : AN.Issue r) : AN.IssueRoot r := AN.issue_root i.
Definition issue_family {r : AN.Result p} (i : AN.Issue r) : option AN.Family := AN.issue_family i.
Definition issue_cause_or_req {r : AN.Result p} (i : AN.Issue r)
  : AN.IssueCause r + AN.UnmetFactRef r := AN.issue_cause_or_req i.
Definition issue_related {r : AN.Result p} (i : AN.Issue r) : list (Index.NodeRef (AN.res_index r)) := AN.issue_related i.
Definition iref_diagnostic {r : AN.Result p} (ref : AN.IssueRef r) : option (AN.Diagnostic r) := AN.iref_diagnostic ref.
Definition iref_boundary {r : AN.Result p} (ref : AN.IssueRef r) : option (AN.Boundary r) := AN.iref_boundary ref.

(* bidirectional membership: a ref is exactly a position indexing an issue in the one sequence *)
Lemma issue_membership_sound (r : AN.Result p) (ref : AN.IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (AN.issue_ref_sound r ref). Qed.
Lemma issue_membership_complete (r : AN.Result p) (n : nat) (i : AN.Issue r) :
  nth_error (result_issues r) n = Some i -> exists ref : AN.IssueRef r, ir_ord ref = n /\ ir_row ref = i.
Proof. exact (AN.issue_ref_complete r n i). Qed.
(* exact identity: the ordinal alone determines the issue *)
Lemma issue_identity (r : AN.Result p) (a b : AN.IssueRef r) : ir_ord a = ir_ord b -> ir_row a = ir_row b.
Proof. exact (AN.issue_ref_ord_identity r a b). Qed.
(* class partition: the sequence is the diagnostics block then the boundaries block *)
Lemma issue_class_partition (r : AN.Result p) :
  result_issues r = map AN.IDiag (AN.result_diagnostics r) ++ map AN.IBound (AN.result_boundaries r).
Proof. exact (AN.result_issues_class_split r). Qed.
(* no collapse: every diagnostic and boundary occupies its own ordinal slot, none merged *)
Lemma issue_no_collapse (r : AN.Result p) :
  Datatypes.length (result_issues r)
  = (Datatypes.length (AN.result_diagnostics r) + Datatypes.length (AN.result_boundaries r))%nat.
Proof. exact (AN.result_issues_length r). Qed.
(* payload: the row a ref names is a canonical row of its class, never fabricated *)
Lemma issue_payload (r : AN.Result p) (ref : AN.IssueRef r) :
  match ir_row ref with AN.IDiag d => In d (AN.result_diagnostics r) | AN.IBound b => In b (AN.result_boundaries r) end.
Proof. exact (AN.iref_payload r ref). Qed.
(* stable order: the k-th diagnostic at ordinal k; the j-th boundary at ordinal (#diagnostics + j) *)
Lemma issue_stable_diag (r : AN.Result p) (n : nat) (d : AN.Diagnostic r) :
  nth_error (AN.result_diagnostics r) n = Some d -> nth_error (result_issues r) n = Some (AN.IDiag d).
Proof. exact (AN.issue_diag_at r n d). Qed.
Lemma issue_stable_bound (r : AN.Result p) (n : nat) (b : AN.Boundary r) :
  nth_error (AN.result_boundaries r) n = Some b ->
  nth_error (result_issues r) ((Datatypes.length (AN.result_diagnostics r) + n)%nat) = Some (AN.IBound b).
Proof. exact (AN.issue_bound_at r n b). Qed.

End IssueReport.

(* bp-free descriptive views the controls read: a one-way projection of the exact cause/requirement, no bp in type *)
Inductive CauseView : Type :=
| CvInvalidIdentity : Names.PredeclaredName -> CauseView
| CvInvalidAppIdentity : Names.PredeclaredName -> CauseView
| CvUnresolvedName : CauseView
| CvTypeAsValue : option Names.PredeclaredName -> CauseView
| CvComplexMismatch : CauseView
| CvMainArity : CauseView
| CvShortDuplicate : Names.OrdinaryIdentifier -> CauseView
| CvShortCountMismatch : nat -> nat -> CauseView
| CvShortReusesNonvar : nat -> nat -> CauseView
| CvShortNoNew : CauseView
| CvNoValueUsed : CauseView
| CvNotCallableExpr : CauseView
| CvNotCallable : CauseView
| CvDefaultOverflow : CauseView
| CvIllegalStatement : CauseView
| CvConversionOverflow : CauseView
| CvConversionNotRepresentable : CauseView
| CvUnaryMismatch : CauseView
| CvOtherCause : CauseView.
Inductive ReqView : Type :=
| RvComplexType : ReqView
| RvShortUsage : ReqView
| RvShortRhsMeaning : nat -> ReqView
| RvShortRedeclTypes : ReqView
| RvSourceTypeApp : ReqView
| RvSourceValueApp : ReqView
| RvShortOriginApp : ReqView
| RvApplication : ReqView
| RvOtherReq : ReqView.

(* bp-free descriptive views of the exact package decision cases: the package's identity, the colliding root entry *)
Record MissingMainView : Type := mk_missing_main_view {
  mmv_package : list String.string ;
  mmv_exec    : String.string
}.
Record CollisionView : Type := mk_collision_view {
  cv_package  : list String.string ;
  cv_exec     : String.string ;
  cv_root     : String.string ;
  cv_root_dir : bool
}.
Definition missing_main_view {p} {r : AN.Result p} (mmr : AN.MissingMainRef r) : MissingMainView :=
  mk_missing_main_view (PI.pkg_components (AN.mmr_package mmr)) (PI.default_exec_name (AN.mmr_package mmr)).
Definition collision_view {p} {r : AN.Result p} (cr : AN.CollisionRef r) : CollisionView :=
  mk_collision_view (PI.pkg_components (AN.cr_package cr)) (PI.default_exec_name (AN.cr_package cr))
    (PI.re_name (AN.cr_root cr)) (match PI.re_kind (AN.cr_root cr) with PI.RootDir => true | PI.RootFile => false end).
(* one-way package-diagnostic views: a missing-main diagnostic yields a MissingMainView, a collision a CollisionView *)
Definition diag_missing_view {p} {r : AN.Result p} (d : AN.Diagnostic r) : option MissingMainView :=
  match d with AN.DMissingMain mmr => Some (missing_main_view mmr) | _ => None end.
Definition diag_collision_view {p} {r : AN.Result p} (d : AN.Diagnostic r) : option CollisionView :=
  match d with AN.DOutputCollision cr => Some (collision_view cr) | _ => None end.

(* §14/§19.4 the package views project exactly the retained ref's package and (for collision) root, one-way *)
Lemma missing_main_view_exact {p} {r : AN.Result p} (mmr : AN.MissingMainRef r) :
  mmv_package (missing_main_view mmr) = PI.pkg_components (AN.mmr_package mmr).
Proof. reflexivity. Qed.
Lemma collision_view_exact {p} {r : AN.Result p} (cr : AN.CollisionRef r) :
  cv_package (collision_view cr) = PI.pkg_components (AN.cr_package cr)
  /\ cv_root (collision_view cr) = PI.re_name (AN.cr_root cr).
Proof. split; reflexivity. Qed.
Lemma diag_missing_view_exact {p} {r : AN.Result p} (mmr : AN.MissingMainRef r) :
  diag_missing_view (AN.DMissingMain mmr : AN.Diagnostic r) = Some (missing_main_view mmr).
Proof. reflexivity. Qed.
Lemma diag_collision_view_exact {p} {r : AN.Result p} (cr : AN.CollisionRef r) :
  diag_collision_view (AN.DOutputCollision cr : AN.Diagnostic r) = Some (collision_view cr).
Proof. reflexivity. Qed.

Definition object_predeclared {p} {idx : Index.ProgramIndex p} (o : BN.ObjectRef idx) : option Names.PredeclaredName :=
  match o with BN.PredeclaredObject pn => Some pn | BN.SourceObject _ => None end.

Definition cause_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} {site : Index.NodeRef idx} {k : AN.FactKind} (c : AN.Cause bp site k) : CauseView :=
  match c with
  | AN.InvalidIdentity _ pn _ => CvInvalidIdentity pn
  | AN.UnresolvedNameV _ _ _ => CvUnresolvedName
  | AN.UnresolvedNameT _ _ _ => CvUnresolvedName
  | AN.UnresolvedApplicationHead _ _ _ _ _ _ => CvUnresolvedName
  | AN.InvalidApplicationIdentity _ _ _ _ pn _ => CvInvalidAppIdentity pn
  | AN.TypeAsValue _ o _ => CvTypeAsValue (object_predeclared o)
  | AN.ComplexMismatch _ _ _ => CvComplexMismatch
  | AN.MainArity _ _ _ _ _ _ _ _ => CvMainArity
  | AN.ShortDuplicate _ n _ _ _ => CvShortDuplicate n
  | AN.ShortCountMismatch st _ _ => CvShortCountMismatch (Index.Refs.sh_names st) (Index.Refs.sh_values st)
  | AN.ShortReusesNonVariable _ i _ m _ _ => CvShortReusesNonvar i m
  | AN.ShortNoNewName _ _ _ => CvShortNoNew
  | AN.NoValueUsed _ => CvNoValueUsed
  | AN.NotCallableExpr _ => CvNotCallableExpr
  | AN.NotCallable _ _ _ _ _ _ => CvNotCallable
  | AN.DefaultOverflow _ _ => CvDefaultOverflow
  | AN.IllegalStatement _ => CvIllegalStatement
  | AN.ConversionOverflow _ _ _ => CvConversionOverflow
  | AN.ConversionNotRepresentable _ _ _ => CvConversionNotRepresentable
  | AN.UnaryMismatch _ => CvUnaryMismatch
  | _ => CvOtherCause
  end.
Definition issuecause_view {p} {r : AN.Result p} (ic : AN.IssueCause r) : CauseView :=
  match ic with AN.OccCause ifr => cause_view (AN.ifr_cause ifr) | _ => CvOtherCause end.
Definition req_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} {site : Index.NodeRef idx} {k : AN.FactKind} (q : AN.Requirement bp site k) : ReqView :=
  match q with
  | AN.ReqComplexType _ => RvComplexType
  | AN.ReqShortUsage _ _ => RvShortUsage
  | AN.ReqShortRhsMeaning _ j _ _ => RvShortRhsMeaning j
  | AN.ReqShortRedeclarationTypes _ _ => RvShortRedeclTypes
  | AN.ReqSourceTypeApp _ _ _ _ _ _ _ => RvSourceTypeApp
  | AN.ReqSourceValueApp _ _ _ _ _ _ _ => RvSourceValueApp
  | AN.ReqShortOriginApp _ _ _ _ _ _ => RvShortOriginApp
  | AN.ReqApplication _ _ _ _ _ _ _ => RvApplication
  | _ => RvOtherReq
  end.

(* concrete controls read these bp-free occurrence views computed DIRECTLY from fact_list, off the vm_compute path *)
Definition result_cause_views {p} (r : AN.Result p) : list CauseView :=
  flat_map (fun o => match AN.occ_cause o with Some c => [cause_view c] | None => [] end)
           (AN.result_fact_list r).
Definition result_req_views {p} (r : AN.Result p) : list ReqView :=
  flat_map (fun o => match AN.occ_req o with Some q => [req_view q] | None => [] end)
           (AN.result_fact_list r).
(* exact displayed families of the invalid/unmet occurrence facts, read directly and bp-free (Family is an enum) *)
Definition result_diag_families {p} (r : AN.Result p) : list AN.Family :=
  flat_map (fun o => match AN.occ_cause o with Some _ => [AN.fact_family o] | None => [] end)
           (AN.result_fact_list r).
Definition result_bound_families {p} (r : AN.Result p) : list AN.Family :=
  flat_map (fun o => match AN.occ_req o with Some _ => [AN.fact_family o] | None => [] end)
           (AN.result_fact_list r).

(* bp-free descriptive view of a redeclared-group diagnostic: its exact root's name (contexts via result_group_* ) *)
Definition diag_group_name {p} {r : AN.Result p} (d : AN.Diagnostic r) : option Names.OrdinaryIdentifier :=
  match d with @AN.DRedeclaredGroup _ _ n _ => Some n | _ => None end.

(* the descriptive group bundle §20 owns: exact scope and spelling with the group's projected member nodes *)
Record DeclarationGroupView {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type := mk_group_view {
  dgv_scope   : BN.ScopeId s ;
  dgv_name    : Names.OrdinaryIdentifier ;
  dgv_members : list (Index.NodeRef idx)
}.
Arguments mk_group_view {p idx s bd bp} _ _ _.
Arguments dgv_scope {p idx s bd bp} _. Arguments dgv_name {p idx s bd bp} _. Arguments dgv_members {p idx s bd bp} _.

(* one-way projection of a redeclared-group diagnostic: exact scope/name off the root, members via diag_related *)
Definition diag_group_view {p} {r : AN.Result p} (d : AN.Diagnostic r)
  : option (DeclarationGroupView (AN.res_surface r) (AN.res_binds r)) :=
  match d with
  | @AN.DRedeclaredGroup _ _ n root =>
      Some (mk_group_view (projT1 root) n (AN.diag_related (AN.DRedeclaredGroup root : AN.Diagnostic r)))
  | _ => None
  end.

(* §24.4 Report group/member/node projection is exact: the view is the exact root's scope/name and member nodes *)
Lemma diag_group_view_exact {p} {r : AN.Result p}
  (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot (AN.res_binds r) n) :
  diag_group_view (AN.DRedeclaredGroup root : AN.Diagnostic r)
  = Some (mk_group_view (projT1 root) n
            (map (fun m => BN.est_node (BN.es_est m)) (BN.bg_members (BN.rr_group (projT2 root))))).
Proof. reflexivity. Qed.

(* §18 bp-free descriptive view of a child prerequisite: the parent and child sites and kinds, the child neg class *)
Record ChildPrerequisiteView {p} (idx : Index.ProgramIndex p) : Type := mk_child_prereq_view {
  cpv_parent_site : Index.NodeRef idx ;
  cpv_parent_kind : AN.FactKind ;
  cpv_child_site  : Index.NodeRef idx ;
  cpv_child_kind  : AN.FactKind ;
  cpv_neg_class   : AN.NegClass
}.
Arguments mk_child_prereq_view {p idx} _ _ _ _ _.
Arguments cpv_parent_site {p idx} _. Arguments cpv_parent_kind {p idx} _.
Arguments cpv_child_site {p idx} _. Arguments cpv_child_kind {p idx} _. Arguments cpv_neg_class {p idx} _.

(* one-way projection of a child-prerequisite ref: exact parent/child sites+kinds off the edge, child neg class *)
Definition child_prereq_view {p} {r : AN.Result p} {cdfr : AN.ChildDependentFactRef r}
  (cpr : AN.ChildPrerequisiteRef r cdfr) : ChildPrerequisiteView (AN.res_index r) :=
  mk_child_prereq_view (AN.cdfr_site cdfr) AN.StatementKind
    (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) (AN.nfr_class (AN.cpr_neg cpr)).

(* the result's child prerequisites as bp-free views, projected one-way from its exact retained refs *)
Definition result_child_prereq_views {p} (r : AN.Result p) : list (ChildPrerequisiteView (AN.res_index r)) :=
  map (fun x => child_prereq_view (projT2 x)) (AN.result_child_prerequisites r).

(* §19.7 the view projects the exact parent/child sites and kinds and the child negative class, one-way *)
Lemma child_prereq_view_exact {p} {r : AN.Result p} {cdfr : AN.ChildDependentFactRef r}
  (cpr : AN.ChildPrerequisiteRef r cdfr) :
  cpv_parent_site (child_prereq_view cpr) = AN.cdfr_site cdfr
  /\ cpv_parent_kind (child_prereq_view cpr) = AN.StatementKind
  /\ cpv_child_site (child_prereq_view cpr) = AN.cdfr_edge_site cdfr
  /\ cpv_child_kind (child_prereq_view cpr) = AN.cdfr_edge_kind cdfr
  /\ cpv_neg_class (child_prereq_view cpr) = AN.nfr_class (AN.cpr_neg cpr).
Proof. repeat split; reflexivity. Qed.
(* §19.7 the concrete result-level views are exactly the one-way projection of the retained refs *)
Lemma result_child_prereq_views_exact {p} (r : AN.Result p) :
  result_child_prereq_views r = map (fun x => child_prereq_view (projT2 x)) (AN.result_child_prerequisites r).
Proof. reflexivity. Qed.

(* §21.1 bp-free RHS-meaning view: parent statement site, RHS index, child site, and the child Value fact kind *)
Record ShortRhsMeaningView {p} (idx : Index.ProgramIndex p) : Type := mk_srm_view {
  srmv_parent_site : Index.NodeRef idx ;
  srmv_rhs_index   : nat ;
  srmv_child_site  : Index.NodeRef idx ;
  srmv_child_kind  : AN.FactKind
}.
Arguments mk_srm_view {p idx} _ _ _ _.
Arguments srmv_parent_site {p idx} _. Arguments srmv_rhs_index {p idx} _.
Arguments srmv_child_site {p idx} _. Arguments srmv_child_kind {p idx} _.
(* one-way projection: the exact parent and child sites and RHS index off the ref, the child kind fixed to Value *)
Definition short_rhs_meaning_view {p} {r : AN.Result p} (srmr : AN.ShortRhsMeaningRef r)
  : ShortRhsMeaningView (AN.res_index r) :=
  mk_srm_view (Index.Refs.sh_node (AN.ssfr_stmt (AN.srmr_parent srmr))) (AN.srmr_j srmr)
    (AN.nvfr_site (AN.srmr_child srmr)) AN.ValueKind.
(* §21.1 the view projects exactly the parent/child sites, the RHS index, and the Value kind, one-way *)
Lemma short_rhs_meaning_view_exact {p} {r : AN.Result p} (srmr : AN.ShortRhsMeaningRef r) :
  srmv_parent_site (short_rhs_meaning_view srmr) = Index.Refs.sh_node (AN.ssfr_stmt (AN.srmr_parent srmr))
  /\ srmv_rhs_index (short_rhs_meaning_view srmr) = AN.srmr_j srmr
  /\ srmv_child_site (short_rhs_meaning_view srmr) = AN.nvfr_site (AN.srmr_child srmr)
  /\ srmv_child_kind (short_rhs_meaning_view srmr) = AN.ValueKind.
Proof. repeat split; reflexivity. Qed.

(* §21.3 bp-free usage view: parent statement site, the source-ordered New indices, and the final usage tag *)
Record ShortUsageView {p} (idx : Index.ProgramIndex p) : Type := mk_su_view {
  suv_parent_site : Index.NodeRef idx ;
  suv_new_indices : list nat ;
  suv_branch      : ReqView
}.
Arguments mk_su_view {p idx} _ _ _.
Arguments suv_parent_site {p idx} _. Arguments suv_new_indices {p idx} _. Arguments suv_branch {p idx} _.
(* one-way projection: the exact parent site and canonical New-row source indices, tagged as the usage branch *)
Definition short_usage_view {p} {r : AN.Result p} (sur : AN.ShortUsageRef r) : ShortUsageView (AN.res_index r) :=
  mk_su_view (Index.Refs.sh_node (AN.ssfr_stmt (AN.sur_parent sur)))
    (map (@projT1 _ _) (AN.sur_new_rows sur)) RvShortUsage.
(* §21.3 the view projects exactly the parent site, the canonical New indices, and the usage tag, one-way *)
Lemma short_usage_view_exact {p} {r : AN.Result p} (sur : AN.ShortUsageRef r) :
  suv_parent_site (short_usage_view sur) = Index.Refs.sh_node (AN.ssfr_stmt (AN.sur_parent sur))
  /\ suv_new_indices (short_usage_view sur) = map (@projT1 _ _) (AN.sur_new_rows sur)
  /\ suv_branch (short_usage_view sur) = RvShortUsage.
Proof. repeat split; reflexivity. Qed.

(* §21.2 bp-free mixed view: parent site, source-ordered existing indices, the aligned RHS indices, and New indices *)
Record ShortRedeclView {p} (idx : Index.ProgramIndex p) : Type := mk_srd_view {
  srdv_parent_site    : Index.NodeRef idx ;
  srdv_existing_index : list nat ;
  srdv_rhs_index      : list nat ;
  srdv_new_index      : list nat
}.
Arguments mk_srd_view {p idx} _ _ _ _.
Arguments srdv_parent_site {p idx} _. Arguments srdv_existing_index {p idx} _.
Arguments srdv_rhs_index {p idx} _. Arguments srdv_new_index {p idx} _.
(* one-way projection: exact parent site, canonical existing indices, index-aligned RHS indices, New indices *)
Definition short_redecl_view {p} {r : AN.Result p} (srtr : AN.ShortRedeclarationTypesRef r)
  : ShortRedeclView (AN.res_index r) :=
  mk_srd_view (Index.Refs.sh_node (AN.ssfr_stmt (AN.srtr_parent srtr)))
    (map (@projT1 _ _) (AN.srtr_existing_rows srtr)) (map (@projT1 _ _) (AN.srtr_existing_rows srtr))
    (map (@projT1 _ _) (AN.srtr_new_rows srtr)).
(* §21.2 the view projects exactly the parent site, the canonical existing/RHS/New indices, one-way *)
Lemma short_redecl_view_exact {p} {r : AN.Result p} (srtr : AN.ShortRedeclarationTypesRef r) :
  srdv_parent_site (short_redecl_view srtr) = Index.Refs.sh_node (AN.ssfr_stmt (AN.srtr_parent srtr))
  /\ srdv_existing_index (short_redecl_view srtr) = map (@projT1 _ _) (AN.srtr_existing_rows srtr)
  /\ srdv_rhs_index (short_redecl_view srtr) = map (@projT1 _ _) (AN.srtr_existing_rows srtr)
  /\ srdv_new_index (short_redecl_view srtr) = map (@projT1 _ _) (AN.srtr_new_rows srtr).
Proof. repeat split; reflexivity. Qed.

(* §9 bp-free source-variable view: the use site and spelling, and the origin short statement site and lhs index *)
Record SourceVariableView {p} (idx : Index.ProgramIndex p) : Type := mk_svv {
  svv_use_site     : Index.NodeRef idx ;
  svv_name         : Names.OrdinaryIdentifier ;
  svv_origin_site  : Index.NodeRef idx ;
  svv_origin_index : nat
}.
Arguments mk_svv {p idx} _ _ _ _.
Arguments svv_use_site {p idx} _. Arguments svv_name {p idx} _.
Arguments svv_origin_site {p idx} _. Arguments svv_origin_index {p idx} _.
(* one-way projection: exact use site + spelling off the ref, the origin short statement node and its lhs index *)
Definition source_variable_view {p} {r : AN.Result p} (sovr : AN.ShortOriginValueRef r)
  : SourceVariableView (AN.res_index r) :=
  mk_svv (AN.sovr_site sovr) (AN.sovr_name sovr)
    (Index.Refs.sh_node (AN.sovr_origin_stmt sovr)) (AN.sovr_origin_ix sovr).
(* §9.6 the view projects exactly the use site, spelling, origin statement site, and lhs index, one-way *)
Lemma source_variable_view_exact {p} {r : AN.Result p} (sovr : AN.ShortOriginValueRef r) :
  svv_use_site (source_variable_view sovr) = AN.sovr_site sovr
  /\ svv_name (source_variable_view sovr) = AN.sovr_name sovr
  /\ svv_origin_site (source_variable_view sovr) = Index.Refs.sh_node (AN.sovr_origin_stmt sovr)
  /\ svv_origin_index (source_variable_view sovr) = AN.sovr_origin_ix sovr.
Proof. repeat split; reflexivity. Qed.

(* abstract-bp law: view projects the exact predeclared name InvalidIdentity retains; bp free, kernel-cheap *)
Lemma cause_view_invalid_id {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r = Some (BN.PredeclaredObject pn)) :
  cause_view (AN.InvalidIdentity r pn H) = CvInvalidIdentity pn.
Proof. reflexivity. Qed.
