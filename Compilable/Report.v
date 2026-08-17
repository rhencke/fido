(* Report — the projection of the one canonical Analysis issue table into ordered diagnostics and boundaries. *)

From Fido Require Import Syntax Index Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.

(* Report owns no cause, severity, order, or fallback: every member and its order is exactly Analysis's. *)
Section Project.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : AN.FactPhase bp) (pf : AN.PackageFacts bp).

Definition Diagnostic : Type := AN.Diagnostic fp pf.
Definition Boundary : Type := AN.Boundary fp pf.
Definition diagnostics : list Diagnostic := AN.diagnostics fp pf.
Definition boundaries : list Boundary := AN.boundaries fp pf.

(* member projections: each reads the exact canonical Analysis cause / requirement / root, never a reread *)
Definition diag_cause (d : Diagnostic) : AN.IssueCause s := AN.diag_cause fp pf d.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) := AN.diag_related fp pf d.
Definition diag_root (d : Diagnostic) : AN.IssueRoot s := AN.diag_root fp pf d.
Definition bound_req (b : Boundary) : AN.Requirement idx := AN.bound_req fp pf b.
Definition bound_root (b : Boundary) : AN.IssueRoot s := AN.bound_root fp pf b.

End Project.

Arguments Diagnostic {p idx s bp} fp pf.
Arguments Boundary {p idx s bp} fp pf.
