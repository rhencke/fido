(* §25 positive provenance: every resolution/const/short-derived Analysis payload is reachable WITH its exact refs. *)
From Stdlib Require Import List.
From Fido Require Import Names Syntax Index Index.Refs
     Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report.
Import ListNotations.
Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

Section Provenance.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
        {d : BN.PhaseData s} (bp : BN.BindingPhase s d).

(* §25.3 unbound: the cause and the dependent non-result retain the exact unbound resolution *)
Definition prov_unresolved (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None) : AN.Cause bp :=
  AN.UnresolvedName r H1 H2.
Definition prov_dep_unbound (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None) : AN.Dependency bp :=
  AN.DepUnboundName r H1 H2.

(* §25.9 type-as-value / not-callable: the invalidity retains the exact bound resolution and its object evidence *)
Definition prov_typeasvalue (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx)
  (H : BN.resolution_object_view r = Some o) : AN.Cause bp := AN.TypeAsValue r o H.
Definition prov_notcallable (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx)
  (H : BN.resolution_object_view r = Some o) : AN.Cause bp := AN.NotCallable r o H.

(* the predeclared invalid-identity cause retains the exact predeclared resolution at the exact site *)
Definition prov_invalidid (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r = Some (BN.PredeclaredObject pn)) : AN.Cause bp := AN.InvalidIdentity r pn H.

(* §25.8 main arity: the cause retains the exact source-bound function resolution that supplied the fixed main *)
Definition prov_mainarity (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (f : BN.FunctionDeclRef idx)
  (H : BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)))
  (args : list (Index.NodeRef idx)) (cnt : nat) : AN.Cause bp := AN.MainArity r f H args cnt.

(* §25.1/25.2 unique local / package source binding: the requirement retains the exact source-bound resolution *)
Definition prov_reqvalue (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (org : BN.DeclOrigin idx)
  (H : BN.resolution_object_view r = Some (BN.SourceObject org)) : AN.Requirement bp := AN.ReqValueMeaning r org H.

(* §25.4 local redeclaration: the dependent non-result retains the exact redeclared resolution and its root *)
Definition prov_dep_redecl (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (root : BN.RedeclRoot bp n)
  (H : BN.resolution_redecl_root r = Some root) : AN.Dependency bp := AN.DepRedeclaredName r root H.

(* §25.6 short duplicate: the cause retains the exact Binding duplicate decision, not merely the duplicate name *)
Definition prov_shortdup (st : Index.Refs.ShortStmtRef idx) (se : BN.ShortEventRef bp st)
  (n : Names.OrdinaryIdentifier)
  (Hn : BN.short_dup_decision_name (BN.short_duplicate_decision se) = Some n) : AN.Cause bp :=
  AN.ShortDuplicate (BN.short_duplicate_decision se) n eq_refl Hn.

(* §18.2 use context: a redeclared use context retains the exact resolution that yields its exact root *)
Definition prov_usecontext (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n)
  (u : Index.NodeRef idx) (res : BN.ResolutionRef (BN.use_env bp u) n)
  (Hy : BN.resolution_redecl_root res = Some root) : AN.RedeclaredUseRef root :=
  AN.mk_redeclared_use u res Hy.

(* §25.4 Report projection: the descriptive group view is the exact retained root's scope, name and members *)
Definition prov_report_group_name (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n)
  : RP.diag_group_name (AN.DRedeclaredGroup root) = Some n := eq_refl.
Definition prov_report_group_view (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n)
  : RP.diag_group_view (AN.DRedeclaredGroup root)
    = Some (RP.mk_group_view (projT1 root) n (AN.diag_related (AN.DRedeclaredGroup root))) := eq_refl.

End Provenance.
