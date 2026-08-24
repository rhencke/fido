(* Report — the projection of the one canonical Analysis issue table into ordered diagnostics and boundaries. *)

From Stdlib Require Import List.
From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.

(* Report owns no cause, severity, order, or fallback: every member and its order is exactly Analysis's. *)
Section Project.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : AN.FactPhase bp) (pf : AN.PackageFacts bp).

Definition Diagnostic : Type := AN.Diagnostic bp.
Definition Boundary : Type := AN.Boundary bp.
Definition diagnostics : list Diagnostic := AN.diagnostics fp pf.
Definition boundaries : list Boundary := AN.boundaries fp.

(* member projections: each reads the exact field the Analysis row already retains, never a reread or reconstruction *)
Definition diag_cause (d : Diagnostic) : AN.IssueCause bp := AN.diag_cause d.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) := AN.diag_related d.
Definition diag_root (d : Diagnostic) : AN.IssueRoot bp := AN.diag_root d.
Definition bound_req (b : Boundary) : AN.Requirement bp := AN.bound_req b.
Definition bound_root (b : Boundary) : AN.IssueRoot bp := AN.bound_root b.

(* exact projection: Report's diagnostics/boundaries ARE Analysis's issue lists, same members and order, no repair *)
Lemma diagnostics_exact : diagnostics = AN.diagnostics fp pf.
Proof. reflexivity. Qed.
Lemma boundaries_exact : boundaries = AN.boundaries fp.
Proof. reflexivity. Qed.
Lemma diag_cause_exact : forall d, diag_cause d = AN.diag_cause d.
Proof. reflexivity. Qed.
Lemma bound_req_exact : forall b, bound_req b = AN.bound_req b.
Proof. reflexivity. Qed.

End Project.

Arguments Diagnostic {p idx s bd} bp.
Arguments Boundary {p idx s bd} bp.

(* Report projects the exact ordinal-indexed issue identities of the one retained result, and nothing more. *)
Section IssueReport.
Context {p : Syntax.Program}.

Definition Issue (r : AN.Result p) : Type := AN.Issue (AN.res_binds r).
Definition IssueRef (r : AN.Result p) : Type := AN.IssueRef r.
Definition result_issues (r : AN.Result p) : list (AN.Issue (AN.res_binds r)) := AN.result_issues r.
Definition ir_ord {r : AN.Result p} (ref : AN.IssueRef r) : nat := AN.ir_ord ref.
Definition ir_row {r : AN.Result p} (ref : AN.IssueRef r) : AN.Issue (AN.res_binds r) := AN.ir_row ref.

(* the exact class, root, family, cause-or-requirement, and per-class row an issue projects *)
Definition issue_class {r : AN.Result p} (i : AN.Issue (AN.res_binds r)) : AN.IssueClass := AN.issue_class i.
Definition issue_root {r : AN.Result p} (i : AN.Issue (AN.res_binds r)) : AN.IssueRoot (AN.res_binds r) := AN.issue_root i.
Definition issue_family {r : AN.Result p} (i : AN.Issue (AN.res_binds r)) : option AN.Family := AN.issue_family i.
Definition issue_cause_or_req {r : AN.Result p} (i : AN.Issue (AN.res_binds r))
  : AN.IssueCause (AN.res_binds r) + AN.Requirement (AN.res_binds r) := AN.issue_cause_or_req i.
Definition issue_related {r : AN.Result p} (i : AN.Issue (AN.res_binds r)) : list (Index.NodeRef (AN.res_index r)) := AN.issue_related i.
Definition iref_diagnostic {r : AN.Result p} (ref : AN.IssueRef r) : option (AN.Diagnostic (AN.res_binds r)) := AN.iref_diagnostic ref.
Definition iref_boundary {r : AN.Result p} (ref : AN.IssueRef r) : option (AN.Boundary (AN.res_binds r)) := AN.iref_boundary ref.

(* bidirectional membership: a ref is exactly a position indexing an issue in the one sequence *)
Lemma issue_membership_sound (r : AN.Result p) (ref : AN.IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (AN.issue_ref_sound r ref). Qed.
Lemma issue_membership_complete (r : AN.Result p) (n : nat) (i : AN.Issue (AN.res_binds r)) :
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
Lemma issue_stable_diag (r : AN.Result p) (n : nat) (d : AN.Diagnostic (AN.res_binds r)) :
  nth_error (AN.result_diagnostics r) n = Some d -> nth_error (result_issues r) n = Some (AN.IDiag d).
Proof. exact (AN.issue_diag_at r n d). Qed.
Lemma issue_stable_bound (r : AN.Result p) (n : nat) (b : AN.Boundary (AN.res_binds r)) :
  nth_error (AN.result_boundaries r) n = Some b ->
  nth_error (result_issues r) ((Datatypes.length (AN.result_diagnostics r) + n)%nat) = Some (AN.IBound b).
Proof. exact (AN.issue_bound_at r n b). Qed.

End IssueReport.

(* bp-free descriptive views the controls read: a one-way projection of the exact cause/requirement, no bp in type *)
Inductive CauseView : Type :=
| CvInvalidIdentity : Names.PredeclaredName -> CauseView
| CvUnresolvedName : CauseView
| CvTypeAsValue : option Names.PredeclaredName -> CauseView
| CvComplexMismatch : CauseView
| CvMainArity : CauseView
| CvOtherCause : CauseView.
Inductive ReqView : Type :=
| RvComplexType : ReqView
| RvOtherReq : ReqView.

Definition object_predeclared {p} {idx : Index.ProgramIndex p} (o : BN.ObjectRef idx) : option Names.PredeclaredName :=
  match o with BN.PredeclaredObject pn => Some pn | BN.SourceObject _ => None end.

Definition cause_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (c : AN.Cause bp) : CauseView :=
  match c with
  | AN.InvalidIdentity _ pn _ => CvInvalidIdentity pn
  | AN.UnresolvedName _ _ _ => CvUnresolvedName
  | AN.TypeAsValue _ o _ => CvTypeAsValue (object_predeclared o)
  | AN.ComplexMismatch _ _ => CvComplexMismatch
  | AN.MainArity _ _ _ _ _ => CvMainArity
  | _ => CvOtherCause
  end.
Definition issuecause_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (ic : AN.IssueCause bp) : CauseView :=
  match ic with AN.OccCause c => cause_view c | _ => CvOtherCause end.
Definition req_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (q : AN.Requirement bp) : ReqView :=
  match q with AN.ReqComplexType _ => RvComplexType | _ => RvOtherReq end.

(* per-Result observation lists the concrete controls read: bp-free, projected from the one retained result *)
Definition result_cause_views {p} (r : AN.Result p) : list CauseView :=
  map (fun d => issuecause_view (AN.diag_cause d)) (AN.result_diagnostics r).
Definition result_req_views {p} (r : AN.Result p) : list ReqView :=
  map (fun b => req_view (AN.bound_req b)) (AN.result_boundaries r).

(* bp-free descriptive view of a redeclared-group diagnostic: its exact root's name (contexts via result_group_* ) *)
Definition diag_group_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (d : AN.Diagnostic bp) : option Names.OrdinaryIdentifier :=
  match d with @AN.DRedeclaredGroup _ _ _ _ _ n _ => Some n | _ => None end.

(* abstract-bp law: view projects the exact predeclared name InvalidIdentity retains; bp free, kernel-cheap *)
Lemma cause_view_invalid_id {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r = Some (BN.PredeclaredObject pn)) :
  cause_view (AN.InvalidIdentity r pn H) = CvInvalidIdentity pn.
Proof. reflexivity. Qed.
