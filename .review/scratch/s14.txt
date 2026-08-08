
(* §4 outcomes: every branch is about the exact site; boundaries are root projections only. *)
Theorem supported_fact_is_the_site_fact : forall p (i : Input p) (ph : Phase i) s f h,
  supported_fact (Supported ph s f) h = f.
Proof. Admitted.
Theorem blocked_is_not_supported : forall p (i : Input p) (ph : Phase i) s pred d o,
  ~ IsSupported (Blocked ph s pred d o).
Proof. Admitted.
Theorem listed_boundary_is_root : forall p (c : Core p) b,
  In b (core_boundaries c) ->
  RootRequirement (phase c) (boundary_site (phase c) b) (boundary_requirement (phase c) b).
Proof. Admitted.
Theorem root_boundary_complete : forall p (c : Core p) s (r : SiteRequirement (phase c) s),
  RootRequirement (phase c) s r ->
  exists b, In b (core_boundaries c) /\ boundary_site (phase c) b = s.
Proof. Admitted.
Theorem boundary_views_nodup : forall p (c : Core p),
  NoDup (List.map boundary_view (core_boundaries c)).
Proof. Admitted.
Theorem boundary_order_canonical : forall p (c : Core p),
  Sorted view_lt (List.map boundary_view (core_boundaries c)).
Proof. Admitted.

(* §4.2 the decision exists before a Program does; accepted views are its projections. *)
Theorem requirement_dec_reflects : forall p (i : Input p) (ph : Phase i) s r,
  (exists h, requirement_dec ph s r = left h) <-> RequirementSatisfied ph s r.
Proof. Admitted.
Theorem accepted_satisfies_every_requirement : forall cp s r,
  RequirementSatisfied (accepted_phase cp) s r.
Proof. Admitted.
Theorem boundary_requirement_unsatisfied : forall p (c : Core p) b,
  In b (core_boundaries c) ->
  ~ RequirementSatisfied (phase c) (boundary_site (phase c) b) (boundary_requirement (phase c) b).
Proof. Admitted.
Theorem view_lt_strict : forall a b c, view_lt a b -> view_lt b c -> view_lt a c.
Proof. Admitted.
Theorem view_lt_irrefl : forall a, ~ view_lt a a.
Proof. Admitted.
Theorem view_lt_total : forall a b, view_lt a b \/ a = b \/ view_lt b a.
Proof. Admitted.

(* §5.1 object laws. *)
Theorem object_origin_injective : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Proof. Admitted.
Theorem object_eqb_spec : forall p (i : Input p) (ph : Phase i) (o1 o2 : ObjectRef ph),
  object_eqb o1 o2 = true <-> o1 = o2.
Proof. Admitted.
Theorem predeclared_object_origin : forall p (i : Input p) (ph : Phase i) n,
  object_origin (predeclared_object ph n) = Predeclared p n.
Proof. Admitted.
Theorem source_object_origin : forall p (i : Input p) (ph : Phase i) s,
  object_origin (source_object ph s) = SourceSite p s.
Proof. Admitted.
Theorem every_object_has_one_origin : forall p (i : Input p) (ph : Phase i) (o : ObjectRef ph),
  (exists n, object_origin o = Predeclared p n) \/ (exists s, object_origin o = SourceSite p s).
Proof. Admitted.
Theorem nil_is_its_own_kind : predeclared_kind PNil = NilObject.
Proof. Admitted.

(* §6 the predeclared capability table connects to the exact facts. *)
Theorem admitted_type_object_has_type_meaning : forall cp n t,
  predeclared_capability n = CapNamedType t ->
  inhabited (TypeMeaning cp (predeclared_object (accepted_phase cp) n)).
Proof. Admitted.
Theorem alias_object_targets_exact_type : forall cp n t,
  predeclared_capability n = CapAliasType t ->
  inhabited (TypeMeaning cp (predeclared_object (accepted_phase cp) n)).
Proof. Admitted.
Theorem callable_names_are_exactly_two : forall n,
  predeclared_capability n = CapCallable -> n = PComplex \/ n = PPrintln.
Proof. Admitted.
Theorem missing_capability_is_a_requirement : forall cp n u,
  predeclared_capability n = CapMissing ->
  ~ RequirementSatisfied (accepted_phase cp) (SBinding (source cp) u)
      (NeedValueMeaning (accepted_phase cp) u (predeclared_object (accepted_phase cp) n)).
Proof. Admitted.
Theorem static_variable_retains_its_site : forall cp o (v : StaticVariable cp o),
  exists s, static_variable_site v = s.
Proof. Admitted.

(* §7 the occurrence atom is the exact nth projection. *)
Theorem occurrence_atom_is_nth : forall cp (o : ResultOccurrence cp),
  List.nth_error
    (result_use_atoms (result_use_fact cp (occ_use cp o) (occ_is_result cp o)))
    (occurrence_position o) = Some (occurrence_atom o).
Proof. Admitted.
Theorem c6_result_use_has_one_atom : forall cp u (f : ResultUseFact cp u),
  List.length (result_use_atoms f) = 1%nat.
Proof. Admitted.

(* §8 rules consume the exact ordered argument occurrences. *)
Theorem argument_occurrence_count : forall cp a,
  List.length (app_argument_occurrences cp a) =
  List.length (application_argument_uses a).
Proof. Admitted.
Theorem argument_occurrence_uses_are_the_source_uses : forall cp a,
  List.map (occ_use cp) (app_argument_occurrences cp a) = app_argument_uses cp a.
Proof. Admitted.
Theorem argument_use_parent_is_the_application : forall p (a : ApplicationRef p) u,
  In u (application_argument_uses a) -> direct_parent u = expr_node (application_expr a).
Proof. Admitted.
Theorem conversion_takes_one_argument : forall cp a t (r : ConversionRule cp a t),
  List.length (app_argument_occurrences cp a) = 1%nat.
Proof. Admitted.
Theorem complex_takes_two_arguments : forall cp a (r : ComplexRule cp a),
  List.length (app_argument_occurrences cp a) = 2%nat.
Proof. Admitted.
Theorem application_results_are_the_parent_results : forall cp a,
  result_form (app_parent_fact cp a) =
  FixedResults cp (application_results cp a (accepted_application_rule cp a)).
Proof. Admitted.
Theorem println_result_is_empty : forall cp a c e ci pr,
  accepted_application_rule cp a = ARPrintln cp a c e ci pr ->
  application_results cp a (accepted_application_rule cp a) = [].
Proof. Admitted.
Theorem unary_untyped_result_is_the_negation : forall cp n c c' h1 h2 h3,
  unary_results cp n (URUntyped cp n c c' h1 h2 h3) = [UntypedConstant cp c'].
Proof. Admitted.

(* §9 statement classification is closed: only a println application is eligible. *)
Theorem only_println_is_eligible : forall cp s (k : StatementCall cp s),
  exists a c h1 h2 h3 pr, k = StmtPrintln cp s a c h1 h2 h3 pr.
Proof. Admitted.
Theorem forbidden_builtin_is_definite_failure : forall cp s n,
  builtin_forbidden_as_statement n = true ->
  statement_class cp s = StatementDefiniteFailure cp s (BuiltinNotAStatement n) ->
  forall k : StatementCall cp s, False.
Proof. Admitted.
Theorem forbidden_and_admitted_are_disjoint : forall n,
  builtin_forbidden_as_statement n = true -> builtin_admitted_as_statement n = false.
Proof. Admitted.
Theorem complex_is_forbidden_as_statement : builtin_forbidden_as_statement PComplex = true.
Proof. Admitted.

(* §10 one consumption authority. *)
Theorem plan_consumes_every_source : forall cp s,
  List.length (plan_occurrences cp (consumption_plan (consumption cp s))) =
  List.length (plan_sources cp (consumption_plan (consumption cp s))).
Proof. Admitted.
Theorem const_site_has_const_plan : forall cp (c : ConstSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (ConstSite (source cp) c)) = ConstPlan cp l.
Proof. Admitted.
Theorem var_site_has_var_plan : forall cp (v : VarSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (VarSite (source cp) v)) = VarPlan cp l.
Proof. Admitted.
Theorem short_site_has_short_plan : forall cp (d : ShortDeclRef (source cp)),
  exists l, consumption_plan (consumption cp (ShortSite (source cp) d)) = ShortPlan cp l.
Proof. Admitted.
Theorem short_reuse_is_same_block : forall cp b o t h l e obj,
  In e l -> e = ShortNamed cp b (ShortReuse cp obj) o t h -> SameBlockEarlier_DELETED cp b obj.
Proof. Admitted.

(* §11 dependency objects. *)
Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Proof. Admitted.
Theorem dependency_respects_source_order : forall p (i : Input p) (ph : Phase i) k,
  SourceOrderConstrained (phase_dependency_graph ph k).
Proof. Admitted.
Theorem accepted_dependency_acyclic : forall cp k,
  exists o, phase_dependency_outcome (accepted_phase cp) k = DependencyOrdered _ o.
Proof. Admitted.
Theorem constants_are_not_runtime_units : forall p (c : ConstSpecRef p),
  RuntimeInitUnit (ConstUnit p c) = false.
Proof. Admitted.
Theorem runtime_projection_excludes_constants : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Proof. Admitted.

(* §12 the diagnostic authority is complete and canonically ordered. *)
Theorem site_failure_enters_through_one_constructor : forall p (i : Input p) (ph : Phase i) s f,
  diagnostic_code (AtSiteFailure ph s f) = site_failure_code f.
Proof. Admitted.
Theorem invalid_conversion_survives : forall p (i : Input p) (ph : Phase i) a v t outer,
  diagnostic_code (AtSiteFailure ph (SApplication p a) (FInvalidConversion ph a v t outer))
    = CodeInvalidConversion.
Proof. Admitted.
Theorem missing_main_entry_survives : forall p (i : Input p) (ph : Phase i) k,
  diagnostic_code (MissingMainEntry ph k) = CodeMissingMainEntry.
Proof. Admitted.
Theorem build_output_is_directory_survives : forall p (i : Input p) (ph : Phase i) k s,
  diagnostic_code (BuildOutputIsDirectory ph k s) = CodeBuildOutputIsDirectory.
Proof. Admitted.
Theorem erase_diagnostic_code : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  erased_code (erase_diagnostic d) = diagnostic_code d.
Proof. Admitted.
Theorem erase_diagnostic_primary : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  erased_primary (erase_diagnostic d) = erase_anchor (diagnostic_primary d).
Proof. Admitted.
Theorem unused_local_only_when_analyzed : forall p (c : Core p) v,
  In (AtSiteFailure (phase c) (SVariable p v) (FUnusedLocal (phase c) v)) (core_diagnostics c) ->
  FullyAnalyzedLocal (phase c) v.
Proof. Admitted.
Theorem unused_local_iff : forall p (c : Core p) v,
  FullyAnalyzedLocal (phase c) v -> LocalVariableSite (phase c) v ->
  (In (AtSiteFailure (phase c) (SVariable p v) (FUnusedLocal (phase c) v)) (core_diagnostics c)
   <-> ~ ReadsVariableAt (phase c) v).
Proof. Admitted.

(* §13 exact capability provenance, restored. *)
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).
Proof. Admitted.
Theorem rejected_retains_core : forall p (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaboration_core (elaborate p).
Proof. Admitted.
Theorem outside_retains_core : forall p (o : Outside_ p),
  compile p = OutsideScope p o -> outside_core o = elaboration_core (elaborate p).
Proof. Admitted.
Theorem compile_sound : forall p cp Hcp, compile p = Compiled p cp Hcp -> Admissible p.
Proof. Admitted.
Theorem compile_complete_in_scope : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Proof. Admitted.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Proof. Admitted.

(* §14 rendering: nontrivial predicates and exact outputs. *)
Theorem unary_operand_never_starts_with_minus : forall e,
  ~ StartsWithMinus (render_in UnaryOperandContext e).
Proof. Admitted.
Theorem parens_in_unary_operand_iff_unary : forall e,
  needs_parens UnaryOperandContext e = true <-> exists op x, e = Unary op x.
Proof. Admitted.
Theorem parens_in_head_iff_unary : forall e,
  needs_parens ApplicationHeadContext e = true <-> exists op x, e = Unary op x.
Proof. Admitted.
Theorem no_parens_in_argument : forall e, needs_parens ApplicationArgumentContext e = false.
Proof. Admitted.
Theorem render_double_negation : forall x,
  render_expr (Unary UnaryMinus (Unary UnaryMinus (Name x)))
    = ("-(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.
Theorem render_negated_head_call : forall f x,
  render_expr (Application (Unary UnaryMinus (Name f)) [Name x])
    = ("(-" ++ spelling (ordinary_identifier f) ++ ")(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Proof. Admitted.
Theorem render_file_no_trailing_blank : forall f, NoTrailingBlank (render_file f).
Proof. Admitted.
Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Proof. Admitted.
Theorem predeclared_shadowed : forall cp u s o,
  InnermostDeclaring cp u s -> bound_object (binding_fact cp u) = o ->
  object_origin o = SourceSite (source cp) (binding_site_object_site s).
Proof. Admitted.

End Theorems.
