(* Report — the projection of the one canonical Analysis issue table into ordered diagnostics and boundaries. *)

From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.

(* Report owns no cause, severity, order, or fallback: every member and its order is exactly Analysis's. *)
Section Project.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : AN.FactPhase bp) (pf : AN.PackageFacts bp).

Definition Diagnostic : Type := AN.Diagnostic s.
Definition Boundary : Type := AN.Boundary s.
Definition diagnostics : list Diagnostic := AN.diagnostics fp pf.
Definition boundaries : list Boundary := AN.boundaries fp.

(* member projections: each reads the exact field the Analysis row already retains, never a reread or reconstruction *)
Definition diag_cause (d : Diagnostic) : AN.IssueCause s := AN.diag_cause d.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) := AN.diag_related d.
Definition diag_root (d : Diagnostic) : AN.IssueRoot s := AN.diag_root d.
Definition bound_req (b : Boundary) : AN.Requirement idx := AN.bound_req b.
Definition bound_root (b : Boundary) : AN.IssueRoot s := AN.bound_root b.

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

Arguments Diagnostic {p idx} s.
Arguments Boundary {p idx} s.
