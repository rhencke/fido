(* §25 provenance: every resolution/const/short-derived payload is reachable at its exact site/kind/refs *)
From Stdlib Require Import List.
From Fido Require Import Names Syntax Index Index.Refs
     Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report.
Import ListNotations.
Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

(* §13.1 the sealed Result authority is reachable exactly as specified: analyze is the sole mint of Result q *)
Definition prov_analyze_mint (q : Syntax.Program) : AN.Result q := AN.analyze q.
(* the authority's transparent data index is exactly the one canonical computation, definitionally *)
Definition prov_data_canonical (q : Syntax.Program) (r : AN.Result q) : AN.data_of_result r = AN.result_data q := AN.data_of_result_canonical r.
(* every Result over q IS analyze q: the singleton authority is unique, assumption-free *)
Definition prov_result_unique (q : Syntax.Program) (r : AN.Result q) : r = AN.analyze q := AN.result_unique r.
(* the public projections read the canonical data fields of that one authority, never the opaque token *)
Definition prov_proj_index (q : Syntax.Program) (r : AN.Result q) : AN.res_index r = AN.rd_index (AN.data_of_result r) := eq_refl.
Definition prov_proj_facts (q : Syntax.Program) (r : AN.Result q) : AN.res_facts r = AN.rd_facts (AN.data_of_result r) := eq_refl.
Definition prov_proj_pkg (q : Syntax.Program) (r : AN.Result q) : AN.res_pkg r = AN.rd_pkg (AN.data_of_result r) := eq_refl.

Section Provenance.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
        {d : BN.PhaseData s} (bp : BN.BindingPhase s d).

(* §25.3 unbound value/type use: the value cause and the type-use cause each retain the exact unbound resolution *)
Definition prov_unresolved_v (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None)
  : AN.Cause bp u AN.ValueKind := AN.UnresolvedNameV r H1 H2.
Definition prov_unresolved_t (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None)
  : AN.Cause bp u AN.TypeUseKind := AN.UnresolvedNameT r H1 H2.

(* §25 unbound dependency: the value and application dependent non-results each retain the exact unbound resolution *)
Definition prov_dep_unbound_v (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None)
  : AN.Dependency bp u AN.ValueKind := AN.DepUnboundNameV r H1 H2.
Definition prov_dep_unbound_a (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n)
  (H1 : BN.resolution_object_view r = None) (H2 : BN.resolution_redecl_root r = None)
  : AN.Dependency bp u AN.ApplicationKind := AN.DepUnboundNameA r H1 H2.

(* §25.9 type-as-value / not-callable / not-a-type: the invalidity retains the exact bound resolution and object *)
Definition prov_typeasvalue (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx)
  (H : BN.resolution_object_view r = Some o) : AN.Cause bp u AN.ValueKind := AN.TypeAsValue r o H.
Definition prov_notcallable (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx)
  (H : BN.resolution_object_view r = Some o) : AN.Cause bp u AN.ApplicationKind := AN.NotCallable r o H.
Definition prov_notatype (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx)
  (H : BN.resolution_object_view r = Some o) : AN.Cause bp u AN.TypeUseKind := AN.NotAType r o H.

(* the predeclared invalid-identity cause / invalid-id dependency retain the exact predeclared resolution at the site *)
Definition prov_invalidid (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r = Some (BN.PredeclaredObject pn)) : AN.Cause bp u AN.ValueKind :=
  AN.InvalidIdentity r pn H.
Definition prov_dep_invalidid (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r = Some (BN.PredeclaredObject pn)) : AN.Dependency bp u AN.ApplicationKind :=
  AN.DepInvalidId r pn H.

(* §25.8 main arity: the cause retains the exact source-bound function resolution that supplied the fixed main *)
Definition prov_mainarity (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (f : BN.FunctionDeclRef idx)
  (H : BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)))
  (args : list (Index.NodeRef idx)) (cnt : nat) : AN.Cause bp u AN.ApplicationKind := AN.MainArity r f H args cnt.

(* §25.1/25.2 unique local / package source binding: the requirement retains the exact source-bound resolution *)
Definition prov_reqvalue (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (org : BN.DeclOrigin idx)
  (H : BN.resolution_object_view r = Some (BN.SourceObject org)) : AN.Requirement bp u AN.ValueKind :=
  AN.ReqValueMeaning r org H.

(* §25.4 local redeclaration: the value/application/type-use dependent non-results retain the exact redecl root *)
Definition prov_dep_redecl_v (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (root : BN.RedeclRoot bp n)
  (H : BN.resolution_redecl_root r = Some root) : AN.Dependency bp u AN.ValueKind :=
  AN.DepRedeclaredNameV r root H.
Definition prov_dep_redecl_a (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (root : BN.RedeclRoot bp n)
  (H : BN.resolution_redecl_root r = Some root) : AN.Dependency bp u AN.ApplicationKind :=
  AN.DepRedeclaredNameA r root H.
Definition prov_dep_redecl_t (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r : BN.ResolutionRef (BN.use_env bp u) n) (root : BN.RedeclRoot bp n)
  (H : BN.resolution_redecl_root r = Some root) : AN.Dependency bp u AN.TypeUseKind :=
  AN.DepRedeclaredNameT r root H.

(* §25.6 short duplicate: the cause retains the exact Binding duplicate decision at the exact statement, not a name *)
Definition prov_shortdup (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (se : BN.ShortEventRef bp st)
  (n : Names.OrdinaryIdentifier)
  (Hn : BN.short_dup_decision_name (BN.short_duplicate_decision se) = Some n)
  (Hs : u = Index.Refs.sh_node st) : AN.Cause bp u AN.StatementKind :=
  AN.ShortDuplicate (BN.short_duplicate_decision se) n eq_refl Hn Hs.

(* §16.7 count mismatch: the cause retains the exact statement, its counts a projection, never supplied free *)
Definition prov_short_count (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx)
  (Hs : u = Index.Refs.sh_node st) (Hne : Index.Refs.sh_names st <> Index.Refs.sh_values st)
  : AN.Cause bp u AN.StatementKind := AN.ShortCountMismatch st Hs Hne.
(* §16.6 nonvariable reuse: the cause retains the exact row ref and its prior member ordinal *)
Definition prov_short_nonvar (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (i m : nat)
  (row : BN.ShortDecisionRowRef (BN.short_event bp st) i)
  (Hrow : BN.row_decision row = BN.ShortExistingNonVariableData m) (Hs : u = Index.Refs.sh_node st)
  : AN.Cause bp u AN.StatementKind := AN.ShortReusesNonVariable st i row m Hrow Hs.
(* §16.4 no new name: the cause retains the exact event's canonical no-new decision *)
Definition prov_short_nonew (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx)
  (Hnn : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = false) (Hs : u = Index.Refs.sh_node st)
  : AN.Cause bp u AN.StatementKind := AN.ShortNoNewName st Hnn Hs.
(* §7 the usage requirement is a minimal tag; the exact New rows are the Result-owned ShortUsageRef *)
Definition prov_short_usage (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx)
  (Hs : u = Index.Refs.sh_node st)
  : AN.Requirement bp u AN.StatementKind := AN.ReqShortUsage st Hs.
(* §9.2 RHS meaning residual: the requirement identifies one exact RHS edge and index *)
Definition prov_short_rhs_meaning (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (Hs : u = Index.Refs.sh_node st)
  : AN.Requirement bp u AN.StatementKind := AN.ReqShortRhsMeaning st j edge Hs.
(* §7 the mixed requirement is a minimal tag; the exact rows are the Result-owned ShortRedeclarationTypesRef *)
Definition prov_short_redecl (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx)
  (Hs : u = Index.Refs.sh_node st)
  : AN.Requirement bp u AN.StatementKind := AN.ReqShortRedeclarationTypes st Hs.
(* §16.8 ambiguous dependency: it retains the exact ambiguous row, and that row derives the exact redeclaration root *)
Definition prov_short_ambiguous (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (i a b : nat)
  (row : BN.ShortDecisionRowRef (BN.short_event bp st) i)
  (Hrow : BN.row_decision row = BN.ShortAmbiguousData a b) (Hs : u = Index.Refs.sh_node st)
  : AN.Dependency bp u AN.StatementKind := AN.DepShortAmbiguous st i row a b Hrow Hs.
(* §8.4/§14.4 the exact redeclaration root the ambiguous row's predecessor group yields, derived not supplied *)
Definition prov_short_ambiguous_root (st : Index.Refs.ShortStmtRef idx) (i a b : nat)
  (row : BN.ShortDecisionRowRef (BN.short_event bp st) i)
  (Hrow : BN.row_decision row = BN.ShortAmbiguousData a b)
  : { n : Names.OrdinaryIdentifier & BN.RedeclRoot bp n } :=
  BN.short_ambiguous_root (BN.short_event bp st) i row a b Hrow.
(* §16.9 RHS-child dependency: it retains the exact RHS value/application child edge, never a raw node *)
Definition prov_short_value_child (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (Hs : u = Index.Refs.sh_node st)
  : AN.Dependency bp u AN.StatementKind := AN.DepChild (AN.ShortValueChild st j edge Hs).
Definition prov_short_app_child (u : Index.NodeRef idx) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (ar : Index.Refs.AppRef idx) (Hs : u = Index.Refs.sh_node st)
  (Ha : Index.Refs.app_node ar = Index.Edges.sr_child edge)
  : AN.Dependency bp u AN.StatementKind := AN.DepChild (AN.ShortApplicationChild st j edge ar Hs Ha).
(* §8.6 the exact positive structural verdict: the five exact local-legality facts, prior to declared-and-used *)
Definition prov_short_valid (st : Index.Refs.ShortStmtRef idx)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None)
  (Hc : Index.Refs.sh_names st = Index.Refs.sh_values st)
  (Hblk : BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true)
  (Hmix : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = false)
  : AN.ShortStructurallyValid bp st := AN.mkShortValid Hdup Hc Hblk Hnew Hmix.

(* §18.2 use context: a redeclared use context retains the exact resolution that yields its exact root *)
Definition prov_usecontext (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n)
  (u : Index.NodeRef idx) (res : BN.ResolutionRef (BN.use_env bp u) n)
  (Hy : BN.resolution_redecl_root res = Some root) : AN.RedeclaredUseRef root :=
  AN.mk_redeclared_use u res Hy.

(* §25.4 Report projection: the descriptive group view is the exact retained root's scope, name and members *)
Definition prov_report_group_name (rr : AN.Result p) (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot (AN.res_binds rr) n)
  : RP.diag_group_name (AN.DRedeclaredGroup root : AN.Diagnostic rr) = Some n := eq_refl.
Definition prov_report_group_view (rr : AN.Result p) (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot (AN.res_binds rr) n)
  : RP.diag_group_view (AN.DRedeclaredGroup root : AN.Diagnostic rr)
    = Some (RP.mk_group_view (projT1 root) n (AN.diag_related (AN.DRedeclaredGroup root : AN.Diagnostic rr))) := eq_refl.

End Provenance.

(* §20 decisive child-prerequisite fixtures: each exact-ref chain is reachable at its exact site/kind/case of r *)
Section ChildPrereq.
Context {p : Syntax.Program} (r : AN.Result p).

(* §20 the two exact expression-statement child edges: the value child, and the application child with exact AppRef *)
Definition fix_value_edge (pr : Index.Refs.ExprStmtRef (AN.res_index r))
  : AN.ChildFactEdge (Index.Refs.exs_node pr) AN.StatementKind := AN.ExprStmtValueChild pr eq_refl.
Definition fix_app_edge (pr : Index.Refs.ExprStmtRef (AN.res_index r)) (ar : Index.Refs.AppRef (AN.res_index r))
  (Ha : Index.Refs.app_node ar = Index.Edges.ee_child (Index.Edges.exprstmt_expr pr))
  : AN.ChildFactEdge (Index.Refs.exs_node pr) AN.StatementKind := AN.ExprStmtApplicationChild pr ar eq_refl Ha.

(* §20 the exact child-dependent parent: a retained statement row whose outcome is SDependent of a DepChild edge *)
Definition fix_cdfr (row : AN.FactRowRef r) (nd : Index.NodeRef (AN.res_index r))
  (edge : AN.ChildFactEdge nd AN.StatementKind)
  (Hok : AN.frr_row row = AN.OFStmt nd (AN.SDependent (AN.DepChild edge))) : AN.ChildDependentFactRef r :=
  AN.mk_cdfr row nd edge Hok.

(* §20.1 value-invalid child: the retained value row's exact InvalidIdentity is the prerequisite's negative case *)
Definition fix20_1_value_invalid (cdfr : AN.ChildDependentFactRef r)
  (child_row : AN.FactRowRef r)
  (Hlk : AN.fact_row_for r (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) = Some child_row)
  (c : AN.Cause (AN.res_binds r) (AN.frr_site child_row) (AN.frr_kind child_row))
  (Hc : AN.occ_cause (AN.frr_row child_row) = Some c) : AN.ChildPrerequisiteRef r cdfr :=
  AN.mk_cpr child_row Hlk (AN.ChildInvalid c Hc).
(* §20.2 value-unmet child: the retained value row's exact requirement is the prerequisite's negative case *)
Definition fix20_2_value_unmet (cdfr : AN.ChildDependentFactRef r)
  (child_row : AN.FactRowRef r)
  (Hlk : AN.fact_row_for r (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) = Some child_row)
  (q : AN.Requirement (AN.res_binds r) (AN.frr_site child_row) (AN.frr_kind child_row))
  (Hq : AN.occ_req (AN.frr_row child_row) = Some q) : AN.ChildPrerequisiteRef r cdfr :=
  AN.mk_cpr child_row Hlk (AN.ChildUnmet q Hq).
(* §20.3 value-dependent child: the child's own exact dependency is retained, not flattened, as the negative case *)
Definition fix20_3_value_dependent (cdfr : AN.ChildDependentFactRef r)
  (child_row : AN.FactRowRef r)
  (Hlk : AN.fact_row_for r (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) = Some child_row)
  (dd : AN.Dependency (AN.res_binds r) (AN.frr_site child_row) (AN.frr_kind child_row))
  (Hd : AN.occ_dep (AN.frr_row child_row) = Some dd) : AN.ChildPrerequisiteRef r cdfr :=
  AN.mk_cpr child_row Hlk (AN.ChildDependent dd Hd).
(* §20.4/20.5 application-invalid / application-unmet child: the application row's exact case is the negative case *)
Definition fix20_4_app_invalid (cdfr : AN.ChildDependentFactRef r)
  (child_row : AN.FactRowRef r)
  (Hlk : AN.fact_row_for r (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) = Some child_row)
  (c : AN.Cause (AN.res_binds r) (AN.frr_site child_row) (AN.frr_kind child_row))
  (Hc : AN.occ_cause (AN.frr_row child_row) = Some c) : AN.ChildPrerequisiteRef r cdfr :=
  AN.mk_cpr child_row Hlk (AN.ChildInvalid c Hc).
Definition fix20_5_app_unmet (cdfr : AN.ChildDependentFactRef r)
  (child_row : AN.FactRowRef r)
  (Hlk : AN.fact_row_for r (AN.cdfr_edge_site cdfr) (AN.cdfr_edge_kind cdfr) = Some child_row)
  (q : AN.Requirement (AN.res_binds r) (AN.frr_site child_row) (AN.frr_kind child_row))
  (Hq : AN.occ_req (AN.frr_row child_row) = Some q) : AN.ChildPrerequisiteRef r cdfr :=
  AN.mk_cpr child_row Hlk (AN.ChildUnmet q Hq).
(* §20.6 a legal expression statement's nonnegative child row yields no prerequisite — the builder returns None *)
Definition fix20_6_legal (child_row : AN.FactRowRef r)
  (H1 : AN.occ_cause (AN.frr_row child_row) = None) (H2 : AN.occ_req (AN.frr_row child_row) = None)
  (H3 : AN.occ_dep (AN.frr_row child_row) = None) : AN.negative_case r child_row = None :=
  AN.negative_case_none r child_row H1 H2 H3.
(* §20.7 the child site carries a distinct value row and application row: the two kinds are provably different *)
Definition fix20_7_same_site_kinds (site : Index.NodeRef (AN.res_index r))
  (rv ra : AN.FactRowRef r) (Hv : AN.fact_row_for r site AN.ValueKind = Some rv)
  (Ha : AN.fact_row_for r site AN.ApplicationKind = Some ra) : ra <> rv :=
  AN.fact_row_for_kind_distinct r site ra rv Ha Hv.
(* §20.8 structural discriminator: an edge's child is parented at exactly its own statement, never a foreign one *)
Definition fix20_8_edge_parent (pr : Index.Refs.ExprStmtRef (AN.res_index r))
  : Index.node_parent (AN.cfe_child_site (AN.ExprStmtValueChild pr eq_refl)) = Some (Index.Refs.exs_node pr) :=
  Index.Child.ca_node_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr)).
(* §9.1 strict structural progress: an expression-statement child's node position strictly follows its parent's *)
Definition fix_strict_progress (pr : Index.Refs.ExprStmtRef (AN.res_index r))
  : (Index.nr_pos (Index.Refs.exs_node pr)
     < Index.nr_pos (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)))%nat :=
  Index.Child.child_pos_gt_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr)).
(* §9.1 the exact child prerequisite carries that strict progress: parent position < child position *)
Definition fix_cpr_parent_lt (cdfr : AN.ChildDependentFactRef r)
  : (Index.nr_pos (AN.cdfr_site cdfr) < Index.nr_pos (AN.cdfr_edge_site cdfr))%nat :=
  AN.cpr_parent_lt_child r cdfr.
(* §9.2 and therefore the parent and child NodeRefs are unequal — genuine structural, not kind/ordinal, distinctness *)
Definition fix_cpr_parent_neq (cdfr : AN.ChildDependentFactRef r)
  : AN.cdfr_site cdfr <> AN.cdfr_edge_site cdfr := AN.cpr_parent_neq_child r cdfr.

End ChildPrereq.
