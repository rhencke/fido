
(* §3 const initializers admit only constant atoms. *)
Theorem const_plan_entries_are_constant : forall cp s l,
  consumption_plan (consumption cp s) = ConstPlan cp l ->
  List.Forall (fun e => ConstAtom cp (occurrence_atom (ce_occurrence cp e))) l.
Proof. Admitted.
Theorem const_site_has_const_plan : forall cp (c : ConstSpecRef (source cp)),
  exists l, consumption_plan (consumption cp (ConstSite (source cp) c)) = ConstPlan cp l.
Proof. Admitted.
Theorem var_site_has_var_plan : forall cp (t : StatementRef (source cp)),
  exists l, consumption_plan (consumption cp (VarSite (source cp) t)) = VarPlan cp l.
Proof. Admitted.
Theorem short_site_has_short_plan : forall cp (t : StatementRef (source cp)),
  exists l, consumption_plan (consumption cp (ShortSite (source cp) t)) = ShortPlan cp l.
Proof. Admitted.

(* §4 statement classification is exact for every C6 case. *)
Theorem println_application_is_eligible : forall cp s a c e ci pr,
  StatementApplication cp s a ->
  accepted_application_rule cp a = ARPrintln cp a c e ci pr ->
  exists h r, statement_class cp s = StatementEligible cp s a h r.
Proof. Admitted.
Theorem forbidden_builtin_is_definite_failure : forall cp s n,
  builtin_forbidden_as_statement n = true ->
  statement_class cp s = StatementDefiniteFailure cp s (BuiltinNotAStatement n) ->
  ~ StatementReq cp s.
Proof. Admitted.
Theorem conversion_is_not_a_statement : forall cp s v,
  statement_class cp s = StatementDefiniteFailure cp s (ConversionNotAStatement v) ->
  ~ StatementReq cp s.
Proof. Admitted.
Theorem non_application_is_not_a_statement : forall cp s rf,
  statement_class cp s = StatementDefiniteFailure cp s (NotAnApplication rf) ->
  ~ StatementReq cp s.
Proof. Admitted.
Theorem forbidden_and_admitted_are_disjoint : forall n,
  builtin_forbidden_as_statement n = true -> builtin_admitted_as_statement n = false.
Proof. Admitted.
Theorem complex_is_forbidden_as_statement : builtin_forbidden_as_statement PComplex = true.
Proof. Admitted.
Theorem println_is_admitted_as_statement : builtin_admitted_as_statement PPrintln = true.
Proof. Admitted.

(* §8 one occurrence authority; every C6 result use selects exactly one. *)
Theorem occurrence_atom_is_the_projection : forall cp (o : ResultOccurrence cp),
  In (occurrence_atom o) (result_use_atoms (occ_fact cp o)).
Proof. Admitted.
Theorem c6_result_use_has_one_atom : forall cp u (f : ResultUseFact cp u),
  List.length (result_use_atoms f) = 1%nat.
Proof. Admitted.
Theorem plan_consumes_every_source : forall cp s,
  List.length (plan_occurrences cp (consumption_plan (consumption cp s))) =
  List.length (consumption_sources (consumption cp s)).
Proof. Admitted.
Theorem plan_covers_site_targets : forall cp s targets,
  SiteTargets cp s targets ->
  plan_targets cp (consumption_plan (consumption cp s)) = targets.
Proof. Admitted.
Theorem short_decl_has_new_name : forall cp s l,
  ShortDeclSite cp s -> consumption_plan (consumption cp s) = ShortPlan cp l ->
  Exists (fun e => match e with
                   | ShortNamed _ _ d _ _ => d = ShortNew cp
                   | ShortBlankEntry _ _ _ => False
                   end) l.
Proof. Admitted.
Theorem short_reuse_is_same_block : forall cp b o t l e obj,
  In e l -> e = ShortNamed cp b (ShortReuse cp obj) o t -> SameBlockEarlier_DELETED cp b obj.
Proof. Admitted.
