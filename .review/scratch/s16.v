
(* §10 static dependency order; only variables project into the C7 store. *)
Theorem dependency_edges_from_bindings : forall p (i : Input p) (ph : Phase i) k,
  EdgesFromBindings (phase_dependency_graph ph k).
Proof. Admitted.
Theorem dependency_respects_source_order : forall p (i : Input p) (ph : Phase i) k,
  SourceOrderConstrained (phase_dependency_graph ph k).
Proof. Admitted.
Theorem accepted_dependency_acyclic : forall cp k,
  exists o, phase_dependency_outcome (accepted_phase cp) k = DependencyOrdered _ o.
Proof. Admitted.
Theorem blank_initializer_is_a_unit : forall p (b : BlankRef p),
  RuntimeInitUnit (BlankUnit p b) = true.
Proof. Admitted.
Theorem constants_are_not_runtime_units : forall p (c : ConstSpecRef p),
  RuntimeInitUnit (ConstUnit p c) = false.
Proof. Admitted.
Theorem runtime_projection_excludes_constants : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Proof. Admitted.
Theorem runtime_projection_preserves_order : forall p (i : Input p) (ph : Phase i) k
  (g : DependencyGraph ph k) (o : AcyclicOrder g),
  runtime_initialization o = List.filter RuntimeInitUnit (order_units o).
Proof. Admitted.

(* §11 diagnostics are complete, anchored and canonically ordered. *)
Theorem diagnostic_anchors_exist : forall p (i : Input p) (ph : Phase i) (d : DiagnosticReason ph),
  exists a, diagnostic_primary d = a.
Proof. Admitted.
Theorem const_initializer_diagnostic_code : forall p (i : Input p) (ph : Phase i) c n r,
  diagnostic_code (ConstInitializerNotConstant ph c n r) = CodeConstInitializerNotConstant.
Proof. Admitted.
Theorem statement_diagnostic_code : forall p (i : Input p) (ph : Phase i) s r,
  diagnostic_code (NotAStatement ph s r) = CodeNotAStatement.
Proof. Admitted.
Theorem unused_local_only_when_analyzed : forall p (c : Core p) s,
  In (UnusedLocal (phase c) s) (core_diagnostics c) -> FullyAnalyzedLocal (phase c) s.
Proof. Admitted.
Theorem unused_local_iff : forall p (c : Core p) s,
  FullyAnalyzedLocal (phase c) s -> LocalVariableSite (phase c) s ->
  (In (UnusedLocal (phase c) s) (core_diagnostics c) <-> ~ ReadsVariableAt (phase c) s).
Proof. Admitted.

(* §12 rendering: exact outputs and token-boundary safety. *)
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
Theorem no_parens_at_top : forall e, needs_parens TopContext e = false.
Proof. Admitted.
Theorem parenthesized_exactly_when_needed : forall ctx e,
  needs_parens ctx e = true -> Parenthesized (render_in ctx e).
Proof. Admitted.
Theorem render_negative_literal :
  render_expr (Unary UnaryMinus (LiteralExpr (IntegerLiteral 1))) = "-1"%string.
Proof. Admitted.
Theorem render_double_negation : forall x,
  render_expr (Unary UnaryMinus (Unary UnaryMinus (Name x)))
    = ("-(-" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.
Theorem render_negated_conversion : forall t x,
  render_expr (Unary UnaryMinus (Application (Name t) [Name x]))
    = ("-" ++ spelling (ordinary_identifier t) ++ "(" ++
       spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.
Theorem render_call : forall f x,
  render_expr (Application (Name f) [Name x])
    = (spelling (ordinary_identifier f) ++ "(" ++ spelling (ordinary_identifier x) ++ ")")%string.
Proof. Admitted.
Theorem render_call_negated_argument : forall f x,
  render_expr (Application (Name f) [Unary UnaryMinus (Name x)])
    = (spelling (ordinary_identifier f) ++ "(-" ++
       spelling (ordinary_identifier x) ++ ")")%string.
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

(* Roots: the three-way decision, and exactness over the in-scope domain. *)
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists h1 h2, decision a = DecisionAccepted (elaboration_core a) h1 h2) <->
  (core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) = []).
Proof. Admitted.
Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists h, decision a = DecisionRejected (elaboration_core a) h) <->
  core_diagnostics (elaboration_core a) <> [].
Proof. Admitted.
Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists h1 h2, decision a = DecisionOutside (elaboration_core a) h1 h2) <->
  (core_diagnostics (elaboration_core a) = [] /\ core_boundaries (elaboration_core a) <> []).
Proof. Admitted.
Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled p cp Hcp -> core_diagnostics (core cp) = [].
Proof. Admitted.
Theorem compile_sound : forall p cp Hcp, compile p = Compiled p cp Hcp -> Admissible p.
Proof. Admitted.
Theorem compile_complete_in_scope : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled p cp Hcp.
Proof. Admitted.
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists f, compile p = Rejected p f.
Proof. Admitted.
Theorem rejected_not_admissible : forall p (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Proof. Admitted.
Theorem outside_asserts_nothing : forall p (o : Outside_ p),
  compile p = OutsideScope p o -> core_boundaries (outside_core o) <> [].
Proof. Admitted.
Theorem scopes_file_order_independent : forall p (i : Input p) (ph : Phase i),
  ScopesFileOrderIndependent ph.
Proof. Admitted.
Theorem predeclared_shadowed : forall cp u s o,
  InnermostDeclaring cp u s -> bound_object (binding_fact cp u) = o ->
  object_origin o = SourceSite (source cp) (binding_site_object_site s).
Proof. Admitted.

End Theorems.
