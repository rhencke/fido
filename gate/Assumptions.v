(* The one assumptions gate: the sole Print Assumptions target, compiled fresh against the built .vo. *)
From Fido Require Import Integer Float Complex FilePath Collections ModulePath Version Syntax Index Typing Compilable Safe Render Emit.

(* the integer family: equality, representability, bounds and distinctness *)
Print Assumptions Integer.equalb_spec.
Print Assumptions Integer.representableb_spec.
Print Assumptions Integer.int_bits_64.
Print Assumptions Integer.uint_bits_64.
Print Assumptions Integer.minimum_representable.
Print Assumptions Integer.maximum_representable.
Print Assumptions Integer.minimum_pred_not_representable.
Print Assumptions Integer.maximum_succ_not_representable.
Print Assumptions Integer.int_neq_int64.
Print Assumptions Integer.uint_neq_uint64.
Print Assumptions Integer.platform_minimum_val.
Print Assumptions Integer.platform_maximum_val.
Print Assumptions Integer.platform_unsigned_maximum_val.

(* the float family: formats, direct rounding, the double-rounding witness and the precision boundaries *)
Print Assumptions Float.kind_equalb_spec.
Print Assumptions Float.precision_f32.
Print Assumptions Float.precision_f64.
Print Assumptions Float.maximum_exponent_f32.
Print Assumptions Float.maximum_exponent_f64.
(* exact rationals: canonicality, reduction, and equality by canonical representation *)
Print Assumptions Float.constant_canonical_intrinsic.
Print Assumptions Float.numerator_denominator_eq.
Print Assumptions Float.constant_equalb_eq.
Print Assumptions Float.constant_equalb_spec.
Print Assumptions Float.constant_of_Z_canonical.
Print Assumptions Float.reduce_constant_canonical.
Print Assumptions Float.reduce_constant_eq.
Print Assumptions Float.constant_canonical_unique.
(* constant conversion: the reflected decision, the scar, overflow, underflow and a source zero *)
Print Assumptions Float.representableb_spec.
(* the decimal literal domain: canonical equality, exact value, the one zero, and a rejected bound *)
Print Assumptions Float.decimal_equalb_spec.
Print Assumptions Float.decimal_value_canonical.
Print Assumptions Float.decimal_value_zero.
Print Assumptions Float.decimal_zero_unique.
(* the runtime float's format-canonical invariant *)
Print Assumptions Float.round_ieee_zero.
Print Assumptions Typing.convert_constant_same_int.
Print Assumptions Typing.typed_int_value.
(* a constant never evaluates to a negative zero *)
Print Assumptions Float.typed_runtime_not_neg_zero.
Print Assumptions Float.typed_runtime_not_nan.
Print Assumptions Float.typed_runtime_not_inf.
Print Assumptions Float.round_typed_float_representable.
Print Assumptions Float.round_constant_typed.
Print Assumptions Typing.convert_constant_same_float.
Print Assumptions Typing.typed_exact.
Print Assumptions Safe.typed_constant_to_value_type.
Print Assumptions Safe.typed_constant_to_value_well_formed.
Print Assumptions Safe.typed_constant_to_value_float.
Print Assumptions Safe.eval_expr_denotes.
Print Assumptions Safe.value_denotes_constant_runtime.
Print Assumptions Safe.float_nonconstant_no_denotes.

(* the complex authority, composed componentwise from the float one *)
Print Assumptions Complex.kind_equalb_spec.
Print Assumptions Complex.component_c64.
Print Assumptions Complex.component_c128.
Print Assumptions Complex.constant_equalb_spec.
Print Assumptions Complex.decimal_value_real.
Print Assumptions Complex.decimal_value_imaginary.
Print Assumptions Complex.round_typed_components.
Print Assumptions Complex.round_typed_real_none.
Print Assumptions Complex.round_typed_imaginary_none.
Print Assumptions Complex.representableb_spec.
Print Assumptions Complex.typed_runtime_real_coherent.
Print Assumptions Complex.typed_runtime_real_shape.
Print Assumptions Complex.typed_runtime_imaginary_shape.
Print Assumptions Complex.typed_runtime_real_not_neg_zero.
Print Assumptions Complex.typed_runtime_real_not_nan.
Print Assumptions Complex.typed_runtime_real_not_inf.

(* the file-path domain: equality, a representable path, and one that has no value at all *)
Print Assumptions FilePath.equalb_spec.

(* the module-path domain: equality, a representable path, and ones that have no value at all *)
Print Assumptions ModulePath.equalb_spec.

(* intrinsic Version: the singleton Go1_23 renders EXACTLY "1.23"; decidable equality *)
Print Assumptions Version.render_go1_23.
Print Assumptions Version.equalb_spec.

(* the collection foundation: the ordered key law and canonical elements of equal maps *)
Print Assumptions Collections.file_path_text_inj.
Print Assumptions Collections.file_elements_equal.

(* the type authority: constant status, defaulting, representability, resolution and program typing *)
Print Assumptions Typing.constant_info_zero_sign.
Print Assumptions Typing.constant_representableb_iff.
Print Assumptions Typing.resolve_sound.
Print Assumptions Typing.resolve_complete.
Print Assumptions Typing.resolve_deterministic.
Print Assumptions Typing.stmt_typedb_iff.
Print Assumptions Typing.program_typedb_iff.
(* map-based typing respects semantic map equality, so construction order cannot change it *)
Print Assumptions Typing.program_equal.
Print Assumptions Typing.program_typedb_equal.
Print Assumptions Typing.program_typedb_build_permutation.
(* the occurrence-stream fold agrees with the existing per-file typing *)
Print Assumptions Compilable.occurrences_file_typedb_eq.
(* the recursive constant analysis reflects the one-node step *)
Print Assumptions Typing.constant_info_step_reflect.
(* string representability, and its non-resolution at an integer type *)
Print Assumptions Typing.string_representable.
Print Assumptions Typing.string_representableb.
(* conversion at use: the untyped route, the same-type identity, and the component reuse pair *)
Print Assumptions Typing.convert_constant_same_complex.
Print Assumptions Typing.convert_complex_reuses_float_component.
Print Assumptions Typing.convert_float_reuses_complex_component.
Print Assumptions Typing.type_untyped_int_convert.
Print Assumptions Typing.type_untyped_float_convert.
Print Assumptions Typing.type_untyped_complex_convert.

(* the source forest: the duplicate-rejecting builder, sound and complete, and its exactness pair *)
Print Assumptions Syntax.files_of_nodes_success_iff_unique.
Print Assumptions Syntax.files_of_nodes_none_iff_duplicate.
Print Assumptions Syntax.files_of_nodes_in.
Print Assumptions Syntax.files_of_nodes_maps_to.
Print Assumptions Syntax.files_of_nodes_mapsto_source.
Print Assumptions Syntax.files_of_nodes_find.
Print Assumptions Syntax.files_of_nodes_duplicate_rejects.
Print Assumptions Syntax.files_of_nodes_duplicate_different_source_rejects.
Print Assumptions Syntax.files_of_nodes_permutation.
Print Assumptions Syntax.build_program_some_iff_unique.
Print Assumptions Syntax.files_equal_refl.
Print Assumptions Syntax.files_equal_sym.
Print Assumptions Syntax.files_equal_trans.

(* admissibility: the executable decision, compile soundness and completeness, and the fixtures *)
Print Assumptions Compilable.semantic_ok_b_source_program_valid.
Print Assumptions Compilable.compile_ok_valid.
Print Assumptions Compilable.compile_complete.
(* provenance and retention: the facts are the accepted core, and the elaborated index is retained *)
Print Assumptions Compilable.compilable_retains_phase.
Print Assumptions Compilable.compilable_retains_expr_facts.
Print Assumptions Compilable.compilable_retains_tnfacts.
Print Assumptions Compilable.program_of_admissible.
Print Assumptions Compilable.capability_source.
Print Assumptions Compilable.capability_is_compile_outcome.
Print Assumptions Compilable.compile_rejected_not_admissible.
(* the sealed mint: one authority-producing operation over a carrier that stays reducible *)
Print Assumptions Emit.Mint.Token.
Print Assumptions Emit.Mint.issue.
Print Assumptions Emit.Mint.module_exact.
Print Assumptions Emit.Mint.files_exact.
Print Assumptions Emit.Image.
Print Assumptions Emit.safe.
Print Assumptions Emit.origin.
Print Assumptions Emit.module_bytes_exact.
Print Assumptions Emit.files_are_exact.
Print Assumptions Emit.provenance.
Print Assumptions Emit.of_safe.
Print Assumptions Emit.of_safe_retains.
Print Assumptions Emit.of_safe_module_bytes.
Print Assumptions Emit.of_safe_files.
Print Assumptions Emit.of_safe_at.
Print Assumptions Emit.of_safe_at_retains.
Print Assumptions Emit.of_safe_at_module_bytes.
Print Assumptions Emit.of_safe_at_files.
Print Assumptions Emit.of_safe_at_refl.
Print Assumptions Emit.of_safe_at_transport.
Print Assumptions Emit.accepted_path_emits_from_returned_capability.
(* the same path on a concrete program, one witness carried from compile through emit *)
Print Assumptions Emit.deep_nested_emit_fixture.
(* package grouping: exactness per file and package, and independence of file order *)
Print Assumptions Compilable.file_in_package.
Print Assumptions Compilable.package_no_empty.
Print Assumptions Compilable.package_summary_main_count.
Print Assumptions Compilable.package_summaries_empty.
Print Assumptions Compilable.package_summaries_equal.
Print Assumptions Compilable.package_summaries_build_permutation.
Print Assumptions Compilable.source_program_valid_files_equal.
Print Assumptions Compilable.reject_no_compile.
Print Assumptions Compilable.compilable_program_typed.
Print Assumptions Compilable.source_program_valid_empty.
(* the package reference: key identity determines it, and the key names a represented package *)
Print Assumptions Compilable.package_ref_present.
Print Assumptions Compilable.package_ref_key_inj.
Print Assumptions Compilable.package_ref_of_binding_key.
Print Assumptions Compilable.package_ref_of_fileref_key.
(* the diagnostic core: an anchor whose kind matches its reason's code *)
Print Assumptions Compilable.diagnostic_code_primary_consistent.
(* diagnostic soundness: each reported code is denoted by the occurrence it names *)
Print Assumptions Compilable.occurrence_expr_diags_conv_sound.
Print Assumptions Compilable.occurrence_expr_diags_default_sound.
(* every enclosing-conversion context is a genuine strict ancestor, same-file, nearest-first and duplicate-free *)
Print Assumptions Compilable.annotate_program_ctx_sound.
Print Assumptions Compilable.annotate_program_ctx_wf.
Print Assumptions Compilable.expression_diags_conversion_single_rounding_sound.
Print Assumptions Compilable.expression_diags_conversion_single_rounding_well_formed.
Print Assumptions Compilable.package_diag_of_bucket_missing_sound.
Print Assumptions Compilable.package_diag_of_bucket_dup_sound.
Print Assumptions Compilable.package_diags_dup_sound.
Print Assumptions Compilable.package_diags_dup_precedence.
Print Assumptions Compilable.package_diags_missing_sound.
(* the keyed visit stream depends only on the file map *)
Print Assumptions Compilable.keyed_visit_files_equal.
(* two programs with the same file map produce the identical erased report *)
Print Assumptions Compilable.annotate_encl_erased.
Print Assumptions Compilable.program_package_erased_find.
Print Assumptions Compilable.erased_expr_diags_source.
Print Assumptions Compilable.erased_pkg_diags_files_equal.
Print Assumptions Compilable.erased_report_files_equal.
(* the erased report carries the planned output name, so different collisions stay distinguishable *)
Print Assumptions Compilable.erase_diagnostic_output.
Print Assumptions Compilable.erased_output_iff_build_output.
Print Assumptions Compilable.erased_fresh_report_of_sole.
(* a permuted file-node list yields the identical erased report *)
Print Assumptions Compilable.erased_report_build_permutation.
(* the expression fact table depends only on the file map *)
Print Assumptions Compilable.program_expr_facts_enum_files_equal.
(* the single-pass fact map agrees with the per-node specification, with no overwrite *)
Print Assumptions Compilable.visit_file_key_nodup.
Print Assumptions Compilable.program_visit_key_nodup.
Print Assumptions Compilable.program_expr_facts_find.
Print Assumptions Compilable.program_expr_facts_eq_spec.
(* the retained production path: one input, one work forest, and total queries over both *)
Print Assumptions Compilable.occurrences_file_operand.
Print Assumptions Compilable.input_visit_ok.
Print Assumptions Compilable.type_name_fact_at_table_resolves.
Print Assumptions Compilable.build_type_name_map.
Print Assumptions Compilable.forest_items_exact.
Print Assumptions Compilable.forest_reverse.
Print Assumptions Compilable.forest_forward.
Print Assumptions Compilable.forest_keys_nodup.
Print Assumptions Compilable.forest_operand_in_tail.
(* work-member identity delegates to the standard map, so no keyed list scan remains in the lookup path *)
Print Assumptions Compilable.work_index_map.
Print Assumptions Compilable.work_index_fresh.
Print Assumptions Compilable.work_index_add_fresh.
Print Assumptions Compilable.work_index_exact.
Print Assumptions Compilable.build_work_index.
Print Assumptions Compilable.forest_index.
Print Assumptions Compilable.index_exact.
Print Assumptions Compilable.index_domain.
Print Assumptions Compilable.index_key_inj.
Print Assumptions Compilable.forest_key_inj.
Print Assumptions Compilable.index_member_at.
Print Assumptions Compilable.index_member_at_retained.
Print Assumptions Compilable.index_no_foreign.
Print Assumptions Compilable.index_nonexpr_absent.
Print Assumptions Compilable.forest_index_member_at.
Print Assumptions Compilable.forest_index_member_at_retained.
Print Assumptions Compilable.forest_index_no_foreign.
Print Assumptions Compilable.build_conversion_work.
(* the outcome table is the causal object: each member's exact insertion cause projects out of the retained trace *)
Print Assumptions Compilable.total_forest_outcome_cause.
Print Assumptions Compilable.final_operand_outcome.
Print Assumptions Compilable.retained_conversion_closure.
Print Assumptions Compilable.conversion_failure_cause_yields_step.
Print Assumptions Compilable.child_failure_cause_yields_member.
Print Assumptions Compilable.conversion_success_cause_yields_step.
Print Assumptions Compilable.build_outcome_trace.
Print Assumptions Compilable.trace_retained_cause.
Print Assumptions Compilable.trace_match.
Print Assumptions Compilable.build_conversion_step.
Print Assumptions Compilable.build_forest_outcome_table.
(* the universal cause-owned acceptance theorems, and unique trace insertion per work member *)
Print Assumptions Compilable.retained_convfail_diag.
Print Assumptions Compilable.outcome_trace_unique_step.
Print Assumptions Compilable.trace_currents_eq.
(* the separate specification bridge, which is not production-cause evidence *)
Print Assumptions Compilable.stepcause_matches.
Print Assumptions Compilable.total_forest_outcome_at_matches.
(* the outcome table's domain is exactly the retained forest's keys, so an extra key is uninhabitable *)
Print Assumptions Compilable.outcomes_present.
Print Assumptions Compilable.outcomes_domain_iff_forest.
Print Assumptions Compilable.outcomes_nonexpr_absent.
(* the total fact and diagnostic projections equal the declarative specification, with no fail-open case *)
Print Assumptions Compilable.forest_facts_eq_spec.
Print Assumptions Compilable.forest_awork_diags_eq.
Print Assumptions Compilable.expression_diagnostics_eq_spec.
Print Assumptions Compilable.expression_diags_eq_spec.
(* the one retained annotated work object, with its alignment derived from its own carried fold *)
Print Assumptions Compilable.build_annotated_work_forest.
Print Assumptions Compilable.annotated_align_eq.
Print Assumptions Compilable.annotated_forest_erased_source.
(* package main buckets, built as one fold over the delivered visit stream *)
Print Assumptions Compilable.program_package_refs_present.
Print Assumptions Compilable.program_package_refs_bucket_len.
Print Assumptions Compilable.program_package_refs_singleton_on_success.
Print Assumptions Compilable.program_package_refs_belongs.
(* the sealed fact tables admit no forged key, and each valid bucket is the one canonical main *)
Print Assumptions Compilable.program_expr_facts_domain.
Print Assumptions Compilable.package_singleton.
(* the expression-fact query is total and projects the sealed table *)
Print Assumptions Compilable.expression_ref_fact_some.
Print Assumptions Compilable.expression_fact_at_find.
(* the sealed type-name table: total, projecting, and giving the alias pairs equal facts *)
Print Assumptions Compilable.type_name_ref_fact_some.
Print Assumptions Compilable.type_name_fact_at_find.
Print Assumptions Compilable.type_name_fact_at_resolves.
Print Assumptions Compilable.tnfact_byte_uint8_same_type.
Print Assumptions Compilable.tnfact_rune_int32_same_type.
Print Assumptions Compilable.tsyn_byte_neq_uint8.
Print Assumptions Compilable.tsyn_rune_neq_int32.
(* the one closed conjunction pinning all sixteen source-name mappings *)
Print Assumptions Compilable.predeclared_all_sixteen.
(* the conversion target reference, minted through the retained index *)
Print Assumptions Compilable.conversion_target_ref_conv.
(* the conversion operand reference, minted through the retained index *)
Print Assumptions Compilable.conversion_operand_ref_conv.
(* one expression phase: facts and diagnostics are both projections of the same retained table *)
Print Assumptions Compilable.facts_and_diags_share_phase.
Print Assumptions Compilable.core_seals_tnfacts.
(* the dependent object chain, so a foreign equal-map table is unrepresentable rather than merely rejected *)
Print Assumptions Compilable.expression_facts_is_facts.
Print Assumptions Compilable.erased_is_diagnostics.
(* each phase component is the builder applied to the phase's own prior objects *)
Print Assumptions Compilable.phase_ot_consumes_work.
Print Assumptions Compilable.phase_awork_consumes_work.
Print Assumptions Compilable.phase_fact_table_consumes_work_outcomes.
Print Assumptions Compilable.phase_diag_consumes_awork_ot.
(* the fact table sealed into a successful result is the phase's own object, not an equal one *)
Print Assumptions Compilable.core_seals_facts.
(* the sealed type-name table is built from the phase's own input; equal names at distinct occurrences stay distinct *)
Print Assumptions Compilable.repeated_name_distinct_refs.
Print Assumptions Compilable.two_uint8_distinct_target_refs.
(* the deep-nested fixtures: a valid nest reports nothing, and an inner overflow reports exactly once *)
Print Assumptions Compilable.deep_nested_compiles.
Print Assumptions Compilable.deep_nested_no_diags.
Print Assumptions Compilable.deep_fail_one_diag.
(* real phase fixtures, queried through the phase's own diagnostic projection *)
Print Assumptions Compilable.deep_nested_phase_no_diags.
Print Assumptions Compilable.deep_fail_phase_reports.
(* direct production-object queries: the real work forest, its outcomes, and its refusal of a foreign key *)
Print Assumptions Compilable.deep_fail_innermost_convfail.
Print Assumptions Compilable.deep_fail_outer_childfail.
Print Assumptions Compilable.deep_fail_exactly_one_diag.
Print Assumptions Compilable.deep_nested_all_ok.
Print Assumptions Compilable.over_program_failure_retains_rejected_core.
(* the one accepted root: compile returns a capability, and that same witness satisfies the fixture *)
Print Assumptions Compilable.deep_nested_compile_fixture.
Print Assumptions Compilable.twin_capability_retains_distinct_occurrences.
(* the one rejected root: compile rejects, and that same rejection satisfies the fixture *)
Print Assumptions Compilable.deep_fail_compile_fixture.
Print Assumptions Compilable.forest_count_source.
Print Assumptions Compilable.member_at_in_forest.
Print Assumptions Compilable.core_prop_at_source.
(* the core retains the whole elaboration: buckets, layout, plan and both diagnostic lists *)
Print Assumptions Compilable.core_refs_fold_own_visit.
Print Assumptions Compilable.core_raw_diagnostics_consume_retained_refs.
Print Assumptions Compilable.admissible_dec.
Print Assumptions Compilable.compile_rejected_of_inadmissible.
Print Assumptions Compilable.forest_count_source.
Print Assumptions Compilable.core_work_count_source.
Print Assumptions Compilable.member_at_in_forest.
Print Assumptions Compilable.twin_distinct_in_forest.
Print Assumptions Compilable.accepted_package_refs_are_decision_refs.
Print Assumptions Compilable.rejected_package_refs_are_decision_refs.
Print Assumptions Compilable.package_bucket_diagnostics_from_refs.
Print Assumptions Compilable.core_package_diags_canonical.
Print Assumptions Compilable.core_package_refs_canonical.
Print Assumptions Compilable.core_plan_is_fresh_build_plan.
Print Assumptions Compilable.core_raw_semantic.
Print Assumptions Compilable.core_diagnostics_eq_elaboration.
Print Assumptions Compilable.failure_diagnostics.
Print Assumptions Compilable.failure_core.
(* core construction: exactly one of each, stored with its proof of canonicality *)
Print Assumptions Compilable.core_input.
Print Assumptions Compilable.phase.
Print Assumptions Compilable.core_package_refs_from_visit.
Print Assumptions Compilable.core_layout_exact.
Print Assumptions Compilable.core_plan_exact.
Print Assumptions Compilable.core_raw_diagnostics_exact.
Print Assumptions Compilable.core_diagnostics_exact.
(* the decision is the retained diagnostic list being empty or not *)
Print Assumptions Compilable.accepted.
Print Assumptions Compilable.rejected.
(* the one production mint path, and the two facts a witness needs about what it minted *)
Print Assumptions Compilable.capability_of_admissible.
Print Assumptions Compilable.capability_source.
Print Assumptions Compilable.capability_is_compile_outcome.
(* the exposed diagnostics are the retained core's own, definitionally *)
Print Assumptions Compilable.failure_nonempty.
Print Assumptions Compilable.phase_domain_exact.
(* the direct final-to-tail closure and the stored-diagnostic evidence, as public surfaces *)
Print Assumptions Compilable.deep_nested_convsuccess_at.
Print Assumptions Compilable.deep_nested_chain_success_evidence.
(* the exact source occurrence lives in the statement, not only in the proof *)
Print Assumptions Compilable.accepted_conversion_at.
Print Assumptions Compilable.childfail_conversion_at.
Print Assumptions Compilable.deep_fail_innermost_diag.
Print Assumptions Compilable.deep_fail_childfail_at.
(* the general cause-owned predicates the concrete fixtures instantiate *)
Print Assumptions Compilable.rejected_conversion_cause.
Print Assumptions Compilable.retained_convfail_cause.
Print Assumptions Compilable.childfail_conversion_cause.
Print Assumptions Compilable.retained_childfail_cause.
(* the command-ordered list at one node-anchored diagnostic is that same singleton *)
Print Assumptions Compilable.core_diagnostics_of_node_singleton.
(* the direct work-index fixtures, over real programs *)
Print Assumptions Compilable.accepted_conversion_cause.
Print Assumptions Compilable.retained_convsuccess_cause.
(* the typed invalid-conversion reason denotes its code end to end *)
Print Assumptions Compilable.occurrence_expr_diags_conv_sound.
Print Assumptions Compilable.byte_uint8_erased_differ.
Print Assumptions Compilable.rune_int32_erased_differ.
(* decision (expression half): every println argument resolves IFF program_typedb / Typing.Program. *)
Print Assumptions Compilable.expression_all_ok_program_typedb.
Print Assumptions Compilable.expression_all_ok_iff_typed_program.
(* expression completeness: no expression diagnostic exactly when the program types *)
Print Assumptions Compilable.emits_none_program_typedb.
Print Assumptions Compilable.expression_diags_empty_iff.
(* package completeness, and the retained elaboration root *)
Print Assumptions Compilable.sum_main_file.
(* the production package decision captures each factored rule exactly *)
Print Assumptions Compilable.redecl_diags_empty_iff_rules.
Print Assumptions Compilable.missing_diags_empty_iff_rules.
(* the direct factored-root surface *)
Print Assumptions Compilable.package_diags_empty_iff_rules.
Print Assumptions Compilable.semantic_diagnostics_empty_iff.
Print Assumptions Compilable.elaboration_accepted_iff_admissible.
Print Assumptions Compilable.elaboration_rejected_iff_inadmissible.

(* the live source root is the factored one: program typing together with the package rules *)
Print Assumptions Compilable.current_package_rules_exactly_one.
(* the readable specification reflection, for fixtures rather than for the production decision *)
Print Assumptions Compilable.source_spec_package_rules_b_package_rules_valid.
Print Assumptions Compilable.source_spec_valid_b_iff.
(* admissibility includes the pinned build-output preflight, one diagnostic layer at a time *)
Print Assumptions Compilable.preflight_fails_iff.
Print Assumptions Compilable.semantic_diagnostics_empty_iff_source_valid.
Print Assumptions Compilable.fresh_build_diagnostics_nil_iff.
Print Assumptions Compilable.fresh_build_diagnostics_fail_singleton.
Print Assumptions Compilable.elaboration_diagnostics_nil_iff_admissible.
Print Assumptions Compilable.elaboration_diagnostics_eq_semantic.
Print Assumptions Compilable.elaboration_diagnostics_fresh_failure.
(* the plan, the report and the acceptance class all depend on the module spec *)
Print Assumptions Compilable.root_layout_input_equal.
Print Assumptions Compilable.fresh_build_plan_input_equal.
Print Assumptions Compilable.erased_elaboration_report_input_equal.
(* the fresh build plan and root layout are retained, derived once from the retained buckets *)
Print Assumptions Compilable.bucket_keys_eq_selected.
Print Assumptions Compilable.fresh_build_plan_of_buckets.
Print Assumptions Compilable.program_build_plan_retained.
Print Assumptions Compilable.program_root_layout_retained.
(* the complete fresh-root-layout exactness, including the sole go.mod entry *)
Print Assumptions Compilable.root_entry_key_neq_gomod.
Print Assumptions Compilable.root_entry_hval.
Print Assumptions Compilable.root_layout_dir_iff.
Print Assumptions Compilable.root_layout_gomod.
Print Assumptions Compilable.root_layout_gomod_iff.
Print Assumptions Compilable.root_layout_source_iff.
Print Assumptions Compilable.root_layout_domain.
(* the universal package-selection, import-path, executable-name and plan exactness *)
Print Assumptions Compilable.selected_iff_file.
Print Assumptions Compilable.selected_key_is_parent.
Print Assumptions Compilable.package_import_path_nested.
Print Assumptions Compilable.package_import_path_inj.
Print Assumptions Compilable.package_import_path_deterministic.
Print Assumptions Compilable.default_exec_name_nonempty.
Print Assumptions Compilable.fresh_build_plan_exec_nonempty.
Print Assumptions Compilable.fresh_build_plan_zero.
Print Assumptions Compilable.fresh_build_plan_multiple.
Print Assumptions Compilable.fresh_build_plan_single_target.

(* the value semantics: zero agreement, well-formed resolved values, and the projected runtime *)
Print Assumptions Safe.eval_zero_sign_agnostic.
Print Assumptions Safe.eval_expr_resolved.
Print Assumptions Safe.eval_expr_resolved_type.
(* evaluation returns exactly the resolved constant's stored value *)
Print Assumptions Safe.resolved_constant_value_float.
Print Assumptions Safe.eval_expr_resolved_value.
Print Assumptions Safe.eval_projects_stored_float_runtime.
Print Assumptions Safe.value_well_formedb_iff.
Print Assumptions Safe.typed_constant_to_value_denotes.
Print Assumptions Safe.eval_string_value.
Print Assumptions Safe.eval_string_resolved_type.
(* the complex runtime: the projection preserves type, and a non-constant component denotes nothing *)
Print Assumptions Safe.typed_constant_to_value_complex.
Print Assumptions Safe.value_denotes_complex_runtime.
Print Assumptions Safe.eval_projects_stored_complex_runtime.
Print Assumptions Safe.certify_retains_capability.
Print Assumptions Safe.certify_retains_core.

(* rendering: all output ASCII, the denotation root, and its functionality *)
Print Assumptions Render.file_ascii.
(* the import domain is empty, and the renderer consumes it structurally *)
Print Assumptions Render.source_imports_nil.
Print Assumptions Render.imports_nil_bytes.
Print Assumptions Render.expr_ascii.
Print Assumptions Render.const_info_denotes.
Print Assumptions Render.const_info_denotes_functional.
Print Assumptions Render.resolved_expr_denotes.
(* the source type name renders from the retained identifier, so distinct names render distinctly *)
Print Assumptions Render.type_expr_inj.
Print Assumptions Render.conv_byte_neq_uint8.
Print Assumptions Render.conv_rune_neq_int32.
(* float rendering: the canonical spelling, the conversions, and the semantic round trip *)
Print Assumptions Render.decimal_ascii.
Print Assumptions Render.decode_render_decimal.
Print Assumptions Render.float_denotes.
Print Assumptions Render.integer_decimal_faithful.
Print Assumptions Render.positive_no_leading_zero.
Print Assumptions Render.boundary_max.
Print Assumptions Render.boundary_min.
Print Assumptions Render.file_first_line.
Print Assumptions Render.module_file_exact.
Print Assumptions Render.module_file_first_line.
Print Assumptions Render.module_file_ascii.
(* strings: the independent decoder inverts the canonical encoder *)
Print Assumptions Render.string_roundtrip.
Print Assumptions Render.string_literal_ascii.
Print Assumptions Render.string_literal_no_nl_cr.
Print Assumptions Render.hex_escape_exact.
Print Assumptions Render.string_denotes.
Print Assumptions Render.resolved_string_denotes.
(* complex rendering: the keywords, the canonical literal, and its round trip *)
Print Assumptions Render.complex_literal_ascii.
Print Assumptions Render.decode_render_complex_literal.
Print Assumptions Render.cplx_denotes.

(* emission: the public emitter needs a certified program, and the image is go.mod beside the file map *)
Print Assumptions Emit.of_safe_module_file_header.
Print Assumptions Emit.of_safe_module_file_ascii.
Print Assumptions Emit.of_safe_header.
Print Assumptions Emit.of_safe_ascii.
Print Assumptions Emit.image_keys_nodup.
(* rendering over the standard file map preserves the key domain and respects map equality *)
Print Assumptions Emit.file_map_domain.
Print Assumptions Emit.file_map_binding.
Print Assumptions Emit.file_map_equal.
Print Assumptions Emit.entries_equal.
Print Assumptions Emit.transport_order_independent.
(* the image realizes the fresh root layout the plan was computed over *)
Print Assumptions Emit.realizes_fresh_layout.
Print Assumptions Emit.files_are_source_paths.
(* the image realizes the retained layout and the retained plan's output target *)
Print Assumptions Emit.realizes_retained_layout.
Print Assumptions Emit.output_target_of_retained_plan.

(* the occurrence index: the universal source exactness theorem and its consequences *)
Print Assumptions Index.Table.get_empty.
Print Assumptions Index.Table.get_set_same.
Print Assumptions Index.Table.get_set_other.
Print Assumptions Index.build_file_count.
Print Assumptions Index.build_file_source_exact.
Print Assumptions Index.source_occurrence_meta.
Print Assumptions Index.meta_source_occurrence.
Print Assumptions Index.source_absence.
Print Assumptions Index.source_occurrence_unique.
Print Assumptions Index.source_kind_exact.
Print Assumptions Index.source_role_exact.
Print Assumptions Index.source_parent_exact.
Print Assumptions Index.source_subtree_end_exact.
(* structural navigation: well-formedness, ancestry, parent lookup and canonical child enumeration *)
Print Assumptions Index.build_file_wf.
Print Assumptions Index.root_id_canonical.
Print Assumptions Index.root_no_parent.
Print Assumptions Index.nonroot_has_parent.
Print Assumptions Index.parent_unique.
Print Assumptions Index.first_child.
Print Assumptions Index.next_child.
Print Assumptions Index.child_enum.
Print Assumptions Index.child_enum_sound.
Print Assumptions Index.child_enum_reaches.
Print Assumptions Index.child_has_parent.
Print Assumptions Index.parent_has_child.
Print Assumptions Index.children_sorted.
Print Assumptions Index.ancestor_complete.
Print Assumptions Index.interval_ancestry.
Print Assumptions Index.enumeration_nodup.
Print Assumptions Index.enumeration_complete.
Print Assumptions Index.enumeration_sound.
Print Assumptions Index.builder_no_structural_search.
Print Assumptions Index.meta_stores_no_subtree.
(* the sealed reference layer, indexed by the exact program *)
Print Assumptions Index.key_eq_dec.
Print Assumptions Index.key_equalb_spec.
(* outer-index exactness: the derived index is the standard map of the per-file build *)
Print Assumptions Index.outer_get_exact.
Print Assumptions Index.Snapshot.index_program.
Print Assumptions Index.Snapshot.file_of_path.
Print Assumptions Index.Snapshot.ref_of_key.
Print Assumptions Index.Snapshot.ref_meta.
Print Assumptions Index.Snapshot.node_kind.
Print Assumptions Index.Snapshot.parent_of.
Print Assumptions Index.Snapshot.children_of.
Print Assumptions Index.Snapshot.node_at.
Print Assumptions Index.Snapshot.source_occurrence_of_ref.
Print Assumptions Index.Snapshot.node_ref_ext.
Print Assumptions Index.Snapshot.node_kind_spec.
Print Assumptions Index.Snapshot.node_role_spec.
Print Assumptions Index.Snapshot.ref_meta_built.
Print Assumptions Index.Snapshot.containing_file_spec.
Print Assumptions Index.Snapshot.node_ref_key_inj.
Print Assumptions Index.Snapshot.file_ref_path_inj.
Print Assumptions Index.Snapshot.parent_root.
Print Assumptions Index.Snapshot.parent_nonroot.
Print Assumptions Index.Snapshot.parent_same_file.
Print Assumptions Index.Snapshot.children_same_file.
Print Assumptions Index.Snapshot.child_parent.
Print Assumptions Index.Snapshot.parent_child.
Print Assumptions Index.Snapshot.children_of_source_order.
Print Assumptions Index.Snapshot.children_of_nodup.
Print Assumptions Index.Snapshot.ref_of_key_sound.
Print Assumptions Index.Snapshot.ref_of_key_complete.
Print Assumptions Index.Snapshot.file_of_path_complete.
Print Assumptions Index.Snapshot.file_of_path_source.
Print Assumptions Index.Snapshot.ref_of_key_source.
Print Assumptions Index.Snapshot.is_ancestor_ref.
Print Assumptions Index.Snapshot.ref_ancestry.
Print Assumptions Index.Snapshot.ref_meta_matches_source.
Print Assumptions Index.Snapshot.node_kind_matches_source.
Print Assumptions Index.Snapshot.node_role_matches_source.
Print Assumptions Index.Snapshot.node_parent_matches_source.
Print Assumptions Index.Snapshot.node_subtree_end_matches_source.
Print Assumptions Index.Snapshot.source_occ_of_ref_eq.
Print Assumptions Index.Snapshot.node_at_matches_source_view.
Print Assumptions Index.Snapshot.node_parent_ref_matches_source.
(* kind-refined references: sound, complete, mismatch-rejecting, and identified by the erased key *)
Print Assumptions Index.erase_as_kind.
Print Assumptions Index.as_kind_complete.
Print Assumptions Index.as_kind_mismatch.
Print Assumptions Index.noderefof_kind.
Print Assumptions Index.noderefof_key_inj.
(* the root-completeness surfaces: file-reference minting and its rejection cases *)
Print Assumptions Index.Snapshot.file_of_path_sound.
Print Assumptions Index.Snapshot.file_of_path_source_exact.
Print Assumptions Index.Snapshot.ref_of_key_invalid_path.
Print Assumptions Index.Snapshot.ref_of_key_invalid_local.
Print Assumptions Index.Snapshot.noderef_eq_dec.
Print Assumptions Index.Snapshot.file_root_ref_local.
Print Assumptions Index.Snapshot.file_root_ref_file.
Print Assumptions Index.Snapshot.file_refs_same_file.
Print Assumptions Index.Snapshot.file_refs_complete.
Print Assumptions Index.Snapshot.file_refs_nodup.
Print Assumptions Index.Snapshot.file_refs_source_order.
Print Assumptions Index.Snapshot.file_root_ref_in_refs.
Print Assumptions Index.Snapshot.reachable_from_root.
Print Assumptions Index.Snapshot.refs_reachable.
(* the indexed traversal: exact, complete, strictly ordered and duplicate-free *)
Print Assumptions Index.occurrences_file_exact.
Print Assumptions Index.occurrences_file_sorted.
Print Assumptions Index.Snapshot.visit_file_view.
Print Assumptions Index.Snapshot.visit_file_complete.
Print Assumptions Index.Snapshot.visit_file_order.
Print Assumptions Index.Snapshot.visit_file_nodup.
Print Assumptions Index.Snapshot.node_ref_key_eq.
(* support: [view_expr] is Some exactly for a Index.ExpressionKind occurrence (the dependent Index.View). *)
Print Assumptions Index.view_expr_kind.
Print Assumptions Index.kind_view_expr.
(* the retained program phase boundary reuses exactly one elaboration *)
Print Assumptions Index.index_program_syntax.
Print Assumptions Index.indexed_syntax_proj.
(* the canonical occurrence key and its standard map laws *)
Print Assumptions Index.key_compare_equal.
Print Assumptions Index.key_map_add_equal.
Print Assumptions Index.key_map_add_unequal.
Print Assumptions Index.key_map_elements_equal.
(* every typed expression query projects its occurrence's exact analyzed fact *)
Print Assumptions Compilable.expression_fact_at_exact.
(* the report's node-anchored diagnostics appear in strictly ascending canonical order *)
Print Assumptions Compilable.collect_node_input_nodup.
Print Assumptions Compilable.collect_node_buckets_singleton.
Print Assumptions Compilable.semantic_diagnostics_node_strict.
Print Assumptions Compilable.collect_diagnostics_in.
(* the source characterization of the erased report *)
Print Assumptions Compilable.erased_report_src_eq.
