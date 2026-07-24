(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    program-rooted GoProgram -> GoTypes (the one type authority: untyped GoConst resolved through
    {TBool, the integer family TInteger over IntegerType, the float family TFloat over FloatType, the complex
    family TComplex over ComplexType, TString} to
    ProgramTyped over the same AST) ->
    GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import Ints Floats Complexes FilePath Collections ModulePath GoVersion GoAST GoIndex GoTypes GoCompile GoSafe GoRender GoEmit.

(* the ONE integer-family authority: type-equality reflection; the single representability reflection;
   exact 64-bit int/uint; generic min/max accepted and below-min/above-max rejected;
   int<>int64 and uint<>uint64 distinct despite equal ranges; the derived default-int bounds. *)
Print Assumptions Ints.integer_type_eqb_eq.
Print Assumptions Ints.integer_representableb_spec.
Print Assumptions Ints.IInt_bits_64.
Print Assumptions Ints.IUint_bits_64.
Print Assumptions Ints.integer_min_representable.
Print Assumptions Ints.integer_max_representable.
Print Assumptions Ints.integer_min_pred_not_representable.
Print Assumptions Ints.integer_max_succ_not_representable.
Print Assumptions Ints.IInt_neq_IInt64.
Print Assumptions Ints.IUint_neq_IUint64.
Print Assumptions Ints.int_min_val.
Print Assumptions Ints.int_max_val.
Print Assumptions Ints.uint_max_val.

(* the ONE float-family authority (Floats.v, axiom-free over SpecFloat): FloatType equality;
   precision/exponent settings; direct binary32/binary64 rounding of exact rationals; the double-rounding
   counterexample (direct F32 differs from binary64-then-binary32); precision boundaries 2^24+1 / 2^53+1. *)
Print Assumptions Floats.float_type_eqb_eq.
Print Assumptions Floats.float_prec_F32.
Print Assumptions Floats.float_prec_F64.
Print Assumptions Floats.float_emax_F32.
Print Assumptions Floats.float_emax_F64.
(* exact-rational canonicality + equality: every FloatConst is INTRINSICALLY canonical (coprime by the record's
   own well-formedness field), so it is fixed by its numerator/denominator (fc_num_den_eq) and reflected equality
   IS Leibniz equality (fc_eqb_eq); cross-multiplication decides value equality; reduction yields a coprime form
   of the same value; on canonical forms value equality IS Leibniz equality (lowest terms). *)
Print Assumptions Floats.fc_canonical_intrinsic.
Print Assumptions Floats.fc_num_den_eq.
Print Assumptions Floats.fc_eqb_eq.
Print Assumptions Floats.fc_eqb_spec.
Print Assumptions Floats.fc_of_Z_canonical.
Print Assumptions Floats.reduce_fc_canonical.
Print Assumptions Floats.reduce_fc_eq.
Print Assumptions Floats.fc_canonical_unique.
(* the ONE constant-conversion/representability authority: reflected decision; the double-round scar back as
   an exact integer constant; overflow rejects; underflow rounds to canonical +0; a source zero -> +0. *)
Print Assumptions Floats.float_representableb_spec.
(* the intrinsic finite-decimal raw literal domain: equality by canonical representation (proof-irrelevant
   well-formedness); the exact rational value is canonical; the unique (0,0) zero -> unsigned zero; a bound /
   non-canonical fixture rejects. *)
Print Assumptions Floats.dm_eqb_eq.
Print Assumptions Floats.decimal_value_canonical.
Print Assumptions Floats.decimal_value_zero.
Print Assumptions Floats.decimal_zero_unique.
(* the runtime float value's format-canonical invariant: an unsigned-zero constant rounds to +0, never -0
   (representability reflection [float_representableb_spec] is gated once, above). *)
Print Assumptions Floats.round_float_sf_zero.
Print Assumptions GoTypes.convert_const_same_int.
Print Assumptions GoTypes.typed_const_int_value.
(* a constant NEVER evaluates to negative zero (the bare-negative-underflow scar): the constructed runtime
   value strips the sign of a zero, so it is never -0. *)
Print Assumptions Floats.tfc_runtime_not_neg_zero.
Print Assumptions Floats.tfc_runtime_not_nan.
Print Assumptions Floats.tfc_runtime_not_inf.
Print Assumptions Floats.round_typed_float_representable.
Print Assumptions Floats.round_float_const_typed.
Print Assumptions GoTypes.convert_const_same_float.
Print Assumptions GoTypes.typed_const_exact.
Print Assumptions GoSafe.typed_const_to_value_type.
Print Assumptions GoSafe.typed_const_to_value_wf.
Print Assumptions GoSafe.typed_const_to_value_float.
Print Assumptions GoSafe.eval_expr_denotes.
Print Assumptions GoSafe.value_denotes_constant_runtime.
Print Assumptions GoSafe.float_nonconstant_no_denotes.

(* Complexes — the ONE complex-type authority, COMPOSED from the Floats component authority: decidable
   ComplexType equality; the ONE component mapping (C64->F32, C128->F64) sourcing all
   precision; exact ComplexConst equality; the decimal-complex exact value projections; round_typed_complex's
   componentwise results (each rounds ONCE) + representability reflection + component-overflow rejection;
   underflow-to-+0 + no-NaN/Inf/-0 runtime component shape (inherited from TypedFloatConst); the runtime
   component read-back coherence. *)
Print Assumptions Complexes.complex_type_eqb_eq.
Print Assumptions Complexes.complex_component_C64.
Print Assumptions Complexes.complex_component_C128.
Print Assumptions Complexes.complex_const_eqb_eq.
Print Assumptions Complexes.decimal_complex_real.
Print Assumptions Complexes.decimal_complex_imag.
Print Assumptions Complexes.round_typed_complex_components.
Print Assumptions Complexes.round_typed_complex_real_none.
Print Assumptions Complexes.round_typed_complex_imag_none.
Print Assumptions Complexes.complex_representableb_spec.
Print Assumptions Complexes.typed_complex_runtime_real_coh.
Print Assumptions Complexes.typed_complex_runtime_real_shape.
Print Assumptions Complexes.typed_complex_runtime_imag_shape.
Print Assumptions Complexes.typed_complex_runtime_real_not_neg_zero.
Print Assumptions Complexes.typed_complex_runtime_real_not_nan.
Print Assumptions Complexes.typed_complex_runtime_real_not_inf.

(* intrinsic FilePath: decidable equality; a representable canonical path; a rejected (unrepresentable)
   path.  Non-canonical paths have no FilePath value at all — this is unrepresentability, not rejection. *)
Print Assumptions FilePath.fp_eqb_eq.

(* intrinsic ModulePath: decidable equality; a representable canonical module path; rejected
   (unrepresentable) module paths.  Invalid module paths have no ModulePath value at all. *)
Print Assumptions ModulePath.mp_eqb_eq.

(* intrinsic GoVersion: the singleton Go1_23 renders EXACTLY "1.23"; decidable equality *)
Print Assumptions GoVersion.render_goversion_go1_23.
Print Assumptions GoVersion.goversion_eqb_eq.

(* the ONE standard-collection foundation: the [FilePath] ordered key and the standard AVL/positive
   map wrappers are backed by pinned rocq-stdlib [FMapAVL]/[FMapPositive] — Fido authors no map/set.  The
   [FilePath] ordered-type law ([fp_str_inj]) that keys the standard file map is axiom-free, and the sorted
   AVL [elements] of extensionally-equal maps are the SAME canonical list ([filemap_elements_Equal]). *)
Print Assumptions Collections.fp_str_inj.
Print Assumptions Collections.filemap_elements_Equal.

(* GoTypes — the ONE type authority (EVIDENCE over the raw AST): zero-sign constant equality; default-type
   exactness (int / FLOAT->float64); representability reflection; the constant-status analysis [const_info]
   carries the exact value via [const_info_exact], routed through the ONE [convert_const] into an intrinsic
   [TypedConst]/[ResolvedConst] + a representable typed integer value; resolution sound + complete +
   deterministic; statement + program typing reflection. *)
Print Assumptions GoTypes.const_info_zero_sign.
Print Assumptions GoTypes.const_representableb_iff.
Print Assumptions GoTypes.resolve_expr_sound.
Print Assumptions GoTypes.resolve_expr_complete.
Print Assumptions GoTypes.resolve_expr_deterministic.
Print Assumptions GoTypes.stmt_typedb_iff.
Print Assumptions GoTypes.program_typedb_iff.
(* map-based typing is ORDER-INDEPENDENT: it respects semantic map equality (as a Prop and reflected as a
   bool) and is therefore invariant under reordered [build_program] construction. *)
Print Assumptions GoTypes.ProgramTyped_Equal.
Print Assumptions GoTypes.program_typedb_Equal.
Print Assumptions GoTypes.program_typedb_build_permutation.
(* the per-occurrence typing predicate folded over the canonical source occurrence stream equals the
   existing [source_file_typedb].  This occurrence/traversal bridge lives in GoCompile (the sole GoIndex+GoTypes
   meeting point); GoTypes owns the type/constant relation only and imports no GoIndex. *)
Print Assumptions GoCompile.occs_file_typedb_eq.
(* the one-node semantic step: [const_info] reflects [const_info_step] applied to its child's status
   (the reusable one-pass leaf authority; convert_const stays the sole conversion authority). *)
Print Assumptions GoTypes.const_info_step_reflect.
(* the string-representability reflections (cross-kind non-resolution): EVERY string constant is representable
   as TString, and no string constant is representable as an integer. *)
Print Assumptions GoTypes.str_representable.
Print Assumptions GoTypes.str_representableb.
(* the constant-conversion reflections AT USE (convert_const the sole conversion authority): an untyped
   int / float / complex constant types through convert_const (type_untyped_*_convert); a same-type complex
   conversion is the identity (convert_const_same_complex, the universal exact-value erasure); a
   matching-format typed float REUSES the complex real component and a typed complex PROJECTS to that scalar
   float (convert_*_reuses_*_component). *)
Print Assumptions GoTypes.convert_const_same_complex.
Print Assumptions GoTypes.convert_complex_reuses_float_component.
Print Assumptions GoTypes.convert_float_reuses_complex_component.
Print Assumptions GoTypes.type_untyped_int_convert.
Print Assumptions GoTypes.type_untyped_float_convert.
Print Assumptions GoTypes.type_untyped_complex_convert.

(* the map-backed SOURCE FOREST — [GoProgram]'s files are a STANDARD FilePath map ([GoFileMap]).  The
   duplicate-rejecting builder [filemap_of_nodes] is SOUND and COMPLETE (success iff the node paths are
   unique; failure iff a path repeats), its domain is exactly the input paths, and — the EXACTNESS pair — on
   success every input node maps to ITS OWN source ([filemap_of_nodes_maps_to]; a duplicate FAILS the build,
   it never silently overwrites) and every built binding comes from an input node
   ([filemap_of_nodes_mapsto_source]).  The semantic file-map equality is an equivalence.  ONE path authority
   (the map key); [GoFileNode] is construction/view only. *)
Print Assumptions GoAST.filemap_of_nodes_success_iff_unique.
Print Assumptions GoAST.filemap_of_nodes_none_iff_duplicate.
Print Assumptions GoAST.filemap_of_nodes_in.
Print Assumptions GoAST.filemap_of_nodes_maps_to.
Print Assumptions GoAST.filemap_of_nodes_mapsto_source.
Print Assumptions GoAST.filemap_of_nodes_find.
Print Assumptions GoAST.filemap_of_nodes_duplicate_rejects.
Print Assumptions GoAST.filemap_of_nodes_duplicate_different_source_rejects.
Print Assumptions GoAST.filemap_of_nodes_permutation.
Print Assumptions GoAST.build_program_some_iff_unique.
Print Assumptions GoAST.FilesEqual_refl.
Print Assumptions GoAST.FilesEqual_sym.
Print Assumptions GoAST.FilesEqual_trans.

(* GoCompile (A) internal exactness: the executable source decision reflects the LIVE factored source root
   [SourceProgramValid]; go_compile sound + complete against it; a rejected program yields no
   CompilableProgram; the compiled evidence exposes that the same program is typed; the empty program is
   accepted; a concrete integer-family program compiles; an out-of-range and an invalid-nested-conversion
   program are rejected with the honest typing error (and have no CompilableProgram); a concrete string
   program compiles. *)
Print Assumptions GoCompile.semantic_ok_b_SourceProgramValid.
Print Assumptions GoCompile.go_compile_ok_valid.
Print Assumptions GoCompile.go_compile_complete.
(* PROVENANCE + RETENTION: every CompilableProgram's facts ARE elaborate's exact ElaborationOK output
   (no parallel capability path), and it RETAINS the exact elaborated index (the projection retains, never
   reconstructs). *)
Print Assumptions GoCompile.compilable_prov.
Print Assumptions GoCompile.compilable_index_retained.
(* map-based PACKAGE GROUPING via a standard [PackageMap] in ONE [FM.fold]: EXACTNESS (every file
   contributes to its own parent package; no package without a file; a summary's main count IS the sum over
   its files; empty file map -> empty package map) and ORDER-INDEPENDENCE (map-equal file collections and
   permuted construction yield map-equal package summaries, so [GoCompile]/[go_compile]'s accept-or-error
   class is invariant under file insertion order). *)
Print Assumptions GoCompile.file_in_package.
Print Assumptions GoCompile.package_no_empty.
Print Assumptions GoCompile.package_summary_main_count.
Print Assumptions GoCompile.package_summaries_empty.
Print Assumptions GoCompile.package_summaries_Equal.
Print Assumptions GoCompile.package_summaries_build_permutation.
Print Assumptions GoCompile.SourceProgramValid_Equal.
Print Assumptions GoCompile.go_compile_class_Equal.
Print Assumptions GoCompile.go_compile_class_build_permutation.
Print Assumptions GoCompile.reject_no_compile.
Print Assumptions GoCompile.compilable_program_typed.
Print Assumptions GoCompile.SourceProgramValid_empty.
(* PackageRef: a validated package-key absence anchor.  Key identity determines the ref (UIP over the
   boolean membership proof), the key names a represented package, and construction from a binding / file
   reference yields the right key. *)
Print Assumptions GoCompile.package_ref_present.
Print Assumptions GoCompile.package_ref_key_inj.
Print Assumptions GoCompile.package_ref_of_binding_key.
Print Assumptions GoCompile.package_ref_of_fileref_key.
(* structured diagnostic core: the primary anchor is an exact-snapshot handle whose kind matches the
   reason's code (invalid anchor/category combinations are unrepresentable). *)
Print Assumptions GoCompile.diagnostic_code_primary_consistent.
(* END-TO-END diagnostic soundness (each diagnostic DENOTES its reported code): an invalid-conversion
   diagnostic's primary is the occurrence's OWN ExprRef, its syntax IS the explicit conversion to the reported
   target of some operand x, the reported operand status is x's exact ConstInfo, and [convert_const] genuinely
   REJECTS it; a default-not-representable diagnostic is a genuine println argument whose exact untyped constant
   does NOT default and whose target is exactly the Go default; a missing-main (whole report) anchors a
   REPRESENTED package that genuinely contains ZERO DMain declarations; a duplicate-main relates a bucket-tail
   main to the FIRST-in-bucket main, both genuine top-level (func main) declarations in the SAME package. *)
Print Assumptions GoCompile.occ_expr_diags_conv_sound.
Print Assumptions GoCompile.occ_expr_diags_default_sound.
(* the NESTED SCAR: every enclosing-conversion (outer_context) ref of an invalid-conversion diagnostic
   in the whole expression report is a genuine CONVERSION whose subtree STRICTLY contains the primary (a real
   strict-ancestor conversion — node_ref_local < primary <= node_subtree_end), and the outer_context is
   SAME-FILE (as the primary), NEAREST-FIRST (deepest enclosing conversion first), and DUPLICATE-FREE (NoDup);
   delivered by the one-pass annotation and proved sound; never fabricated or copied syntax. *)
Print Assumptions GoCompile.annotate_program_ctx_sound.
Print Assumptions GoCompile.annotate_program_ctx_wf.
Print Assumptions GoCompile.expr_diags_conv_scar_sound.
Print Assumptions GoCompile.expr_diags_conv_scar_wf.
Print Assumptions GoCompile.pkg_diag_of_bucket_missing_sound.
Print Assumptions GoCompile.pkg_diag_of_bucket_dup_sound.
Print Assumptions GoCompile.pkg_diags_dup_sound.
Print Assumptions GoCompile.pkg_diags_dup_precedence.
Print Assumptions GoCompile.pkg_diags_missing_sound.
(* cross-snapshot determinism FOUNDATION: the KEYED visit stream (each visited reference's NodeKey
   + its source occurrence) depends ONLY on the file map, so FilesEqual programs have IDENTICAL keyed streams
   (the basis for equal erased reports / fact enumerations). *)
Print Assumptions GoCompile.keyed_visit_FilesEqual.
(* THE cross-snapshot determinism theorem: two programs with the SAME file map (whose diagnostics
   live in DIFFERENT dependent snapshot types) produce the IDENTICAL erased report — it depends ONLY on the
   file map, never on the snapshot index or the backing AVL shape.  The expression half factors through
   [annotate_source] (the one-pass enclosing context erases to a source function of the keyed stream); the
   package half through the keyed source buckets ([ppkg_erased_find] + PackageMap canonical elements). *)
Print Assumptions GoCompile.annotate_encl_erased.
Print Assumptions GoCompile.ppkg_erased_find.
Print Assumptions GoCompile.erased_expr_diags_source.
Print Assumptions GoCompile.erased_pkg_diags_FilesEqual.
Print Assumptions GoCompile.erased_report_FilesEqual.
(* the erased build-OUTPUT NAME payload: [ed_output] is the reason's exact planned output name
   for a build-output-directory reason and none elsewhere; the erased fresh report of a sole colliding package
   CARRIES that name (so cross-snapshot comparison distinguishes different collision names); concrete "a". *)
Print Assumptions GoCompile.erase_diagnostic_output.
Print Assumptions GoCompile.erased_output_iff_build_output.
Print Assumptions GoCompile.erased_fresh_report_of_sole.
(* construction-permutation corollary: building the same module from a PERMUTED file-node list
   yields the IDENTICAL erased report (the report is invariant to the proposer's file order). *)
Print Assumptions GoCompile.erased_report_build_permutation.
(* SUCCESSFUL-fact enumeration determinism: the expression fact table depends ONLY on the
   file map (source NodeKeys + source-derived values, a fold-map fusion over the keyed stream), so FilesEqual
   programs have the IDENTICAL canonical fact enumeration. *)
Print Assumptions GoCompile.prog_expr_facts_enum_FilesEqual.
(* occurrence-keyed expression facts, built by the SINGLE bottom-up pass: visit_file refs have
   distinct NodeKeys, and the fact stored at a visited ref's key is EXACTLY that occurrence's fact (no
   overwrite; map-level exactness) — the single-pass fact map agrees with the per-node specification. *)
Print Assumptions GoCompile.visit_file_key_nodup.
Print Assumptions GoCompile.prog_visit_key_nodup.
Print Assumptions GoCompile.prog_expr_facts_find.
Print Assumptions GoCompile.prog_expr_facts_eq_spec.
(* §3/§4/§5/§6 the retained-phase production path: the ONE [CompilationInput] retains the visit as a STORED value
   that IS the snapshot's traversal ([ci_visit_ok]); the [TypeNameFactTable] is built from THAT retained visit
   ([build_tnft_map]); the ONE proof-carrying [ExprWorkForest] OBJECT is built ONCE and RETAINS in its fields the
   exact pair-projection ([ewf_items_exact]), BOTH domains ([ewf_reverse] reverse / [ewf_forward] forward), the
   key-NoDup ([ewf_keys_nodup]), with a conversion's operand MEMBER in the PROCESSED suffix
   ([ewf_operand_in_tail]) — no [proj1_sig] discards its proof; the PROOF-CARRYING FOREST-INDEXED
   [ForestOutcomeTable] pairs the outcome map with its completeness proof so the query is TOTAL —
   [total_forest_outcome_at] CONSUMES a retained [WorkMember] and MATCHES the occurrence
   ([total_forest_outcome_at_matches]); the resolved-target query is the table's stored fact
   ([type_name_fact_at_table_resolves]); and a stored conversion FAILURE's cause is read DIRECTLY off the
   retained forest table, keyed by the WORK member — its refs are the work's own carried refs, the target type is
   the sealed table's stored fact, the operand's outcome is read THROUGH the exact operand [SuffixMember]
   ([oa_total acc_rest]) as a success whose status IS the reported one, and [convert_const] genuinely rejects
   ([total_forest_outcome_cause] retaining the member/suffix-indexed [StepCause], inverted by
   [StepCause_convfail_inv]). *)
Print Assumptions GoCompile.occs_file_operand.
Print Assumptions GoCompile.ci_visit_ok.
Print Assumptions GoCompile.type_name_fact_at_table_resolves.
Print Assumptions GoCompile.build_tnft_map.
Print Assumptions GoCompile.ewf_items_exact.
Print Assumptions GoCompile.ewf_reverse.
Print Assumptions GoCompile.ewf_forward.
Print Assumptions GoCompile.ewf_keys_nodup.
Print Assumptions GoCompile.ewf_operand_in_tail.
(* §3/§6 (REPAIR 9) the forest outcome table IS THE INTRINSIC CAUSAL OBJECT: [build_forest_outcome_table] folds the
   [OutcomeTrace] whose cons node RETAINS the exact tail trace + tail accumulator + head member + [StepCause] over
   the EXACT tail ([build_outcome_trace]); the table pairs [fot_acc] with [fot_trace] INDEXED by it (not freely
   pairable).  [total_forest_outcome_cause] PROJECTS the trace ([trace_retained_cause]) to each member's exact
   insertion [RetainedMemberCause] — the exact suffix split, the AUTHENTICATED tail [OutcomeAccumulator], the
   [StepCause] producing the FINAL outcome, and the tail-to-final QUERY PRESERVATION.  The direct cause is projected
   by inverting the [StepCause] (axiom-free); [final_operand_outcome] specializes preservation to a conversion's
   operand, proving its FINAL-table query EQUALS its retained tail query — the final-to-tail closure. *)
Print Assumptions GoCompile.total_forest_outcome_cause.
Print Assumptions GoCompile.final_operand_outcome.
Print Assumptions GoCompile.retained_conversion_closure.
Print Assumptions GoCompile.StepCause_convfail_inv.
Print Assumptions GoCompile.StepCause_childfail_inv.
Print Assumptions GoCompile.StepCause_ok_conv_inv.
Print Assumptions GoCompile.build_outcome_trace.
Print Assumptions GoCompile.trace_retained_cause.
Print Assumptions GoCompile.trace_match.
Print Assumptions GoCompile.build_conversion_step.
Print Assumptions GoCompile.build_forest_outcome_table.
(* §4/§5 (REPAIR 10) the UNIVERSAL acceptance theorems over ANY retained table/member: the direct conversion-success
   closure ([retained_convsuccess_closure] — exact ConversionStep + target fact + operand SuffixMember + tail =
   final = EOOk opf + one convert_const success + exact current fact), the direct child-failure closure +
   no-local-reason ([retained_childfail_closure] — operand fails in tail AND final, current EOChildFail, current
   member emits no diagnostic), the stored-diagnostic connection ([retained_convfail_diag] — the exact
   DRInvalidConversion over the STORED EOConvFail fields is a member of the projected list, read via
   [forest_awork_diags] not [local_conv_failure], returning the exact retained annotated member/context pair whose
   underlying work item IS that member), and UNIQUE trace insertion per work member
   ([outcome_trace_unique_step] — the trace's insertion sequence IS ewf_items, each once, key-NoDup). *)
Print Assumptions GoCompile.retained_convsuccess_closure.
Print Assumptions GoCompile.retained_childfail_closure.
Print Assumptions GoCompile.retained_convfail_diag.
Print Assumptions GoCompile.outcome_trace_unique_step.
Print Assumptions GoCompile.trace_currents_eq.
(* §9.5 the SEPARATE spec bridge (NOT production-cause evidence): a member's [StepCause] AGREES with the index-free
   source specification [outcome_matches] given the operands' matches ([stepcause_matches], by construction in the
   fold); the total query at a retained member matches its own occurrence ([total_forest_outcome_at_matches]). *)
Print Assumptions GoCompile.stepcause_matches.
Print Assumptions GoCompile.total_forest_outcome_at_matches.
(* §7/§2.9 the forest outcome table's domain is EXACTLY the RETAINED work forest's key set: every work item has an
   entry ([fot_present]); the biconditional is over MEMBERSHIP in the retained enumeration [ewf_items]
   ([fot_domain_iff_forest], NOT an [exists w] over any constructible [ExprWork]) — so a table with the required
   entries plus any extra key is UNINHABITABLE; and a visited NON-expression occurrence has NO entry
   ([fot_nonexpr_absent], wrong-kind exclusion). *)
Print Assumptions GoCompile.fot_present.
Print Assumptions GoCompile.fot_domain_iff_forest.
Print Assumptions GoCompile.fot_nonexpr_absent.
(* §9 the TOTAL fact + diagnostic projections of the ONE forest outcome table EQUAL the declarative specification
   (no fail-open: a missing outcome is never a case; the diagnostic emits the STORED refs).  §8/§2.3 the
   diagnostic is projected over the exact RETAINED annotated work ([forest_awork_diags], keyed by the work's own
   [ew_expr_ref] — NO [as_expr] with a fail-open [None] branch); [forest_awork_diags_eq] is its agreement with the
   source spec at the work's own occurrence. *)
Print Assumptions GoCompile.forest_facts_eq_spec.
Print Assumptions GoCompile.forest_awork_diags_eq.
Print Assumptions GoCompile.expression_diagnostics_eq_spec.
Print Assumptions GoCompile.expr_diags_eq_spec.
(* §7 THE ONE RETAINED ANNOTATED WORK OBJECT: [build_annotated_work_forest] constructs an
   [AnnotatedExprWorkForest] carrying (all field proofs axiom-free) the exact-members equality, the
   [annotate_program] fold-equivalence, and the four context-soundness properties; [aewf_align_eq] is the
   occurrence/context alignment derived from the object's OWN carried fold (no rebuild); and
   [annotated_forest_erased_source] is the [aewf_spec_exact] surface — the erased annotation reproduces the
   EXPRESSION projection of the snapshot-independent [annotate_source]. *)
Print Assumptions GoCompile.build_annotated_work_forest.
Print Assumptions GoCompile.aewf_align_eq.
Print Assumptions GoCompile.annotated_forest_erased_source.
(* package main-ref buckets built as ONE fold over the DELIVERED visit stream (no second
   per-file traversal): the whole-program buckets have the represented-package domain, each present bucket's
   length is the package's main count, on a valid program every bucket is a singleton (the one canonical
   main), and every main in a bucket belongs to that package. *)
Print Assumptions GoCompile.prog_package_refs_present.
Print Assumptions GoCompile.prog_package_refs_bucket_len.
Print Assumptions GoCompile.prog_package_refs_singleton_on_success.
Print Assumptions GoCompile.prog_package_refs_belongs.
(* the SEALED fact tables (no forged/foreign key possible): every key with an entry is a visited
   expression occurrence's key whose fact is exact; and on a valid program each package bucket is the one
   canonical main (the ElaborationFacts-level singleton projection). *)
Print Assumptions GoCompile.prog_expr_facts_domain.
Print Assumptions GoCompile.ef_package_singleton.
(* the expression-fact query is TOTAL on a valid ElaborationFacts: every typed ExprRef denotes a
   visited occurrence whose const_info succeeds (so it has an exact entry), and the option-free query PROJECTS
   the sealed table (returns exactly the stored fact — a defect-shipping option result is impossible). *)
Print Assumptions GoCompile.expr_ref_fact_some.
Print Assumptions GoCompile.expr_fact_at_find.
(* §8 the SEALED occurrence-keyed TYPE-NAME fact table: the query is TOTAL (every TypeNameRef has a stored
   entry, needing no validity — a conversion's source name resolves by construction) and PROJECTS the sealed
   table (returns exactly the stored fact); the stored fact EQUALS predeclared resolution of the SOURCE name
   recovered THROUGH the reference (no recompute, no spelling copy); and byte/uint8 (rune/int32) are DISTINCT
   source type syntax with EQUAL resolved-GoType facts. *)
Print Assumptions GoCompile.type_name_ref_fact_some.
Print Assumptions GoCompile.type_name_fact_at_find.
Print Assumptions GoCompile.type_name_fact_at_resolves.
Print Assumptions GoCompile.tnfact_byte_uint8_same_type.
Print Assumptions GoCompile.tnfact_rune_int32_same_type.
Print Assumptions GoCompile.tsyn_byte_neq_uint8.
Print Assumptions GoCompile.tsyn_rune_neq_int32.
(* §5.2 the ONE closed conjunction pinning all SIXTEEN source-name mappings (14 numeric + byte->uint8 +
   rune->int32). *)
Print Assumptions GoCompile.predeclared_all_sixteen.
(* §3.3 the conversion TARGET ref is obtained THROUGH the retained index (minted TypeNameRef): the exact
   RConversionTarget child key, role RConversionTarget, recovering the exact raw source TypeSyntax. *)
Print Assumptions GoCompile.conversion_target_ref_conv.
(* §3.2/§10.2 the conversion OPERAND ref THROUGH the retained index: the exact RConversionOperand child key,
   role RConversionOperand, recovering the exact raw operand. *)
Print Assumptions GoCompile.conversion_operand_ref_conv.
(* §8/§3.8 ONE EXPRESSION PHASE (OBJECT IDENTITY): the sealed FACTS and the DIAGNOSTICS are BOTH projections of
   the SAME retained [ep_ot] outcome table inside one [ExpressionPhase] ([facts_and_diags_share_phase]); and the
   type-name TABLE OBJECT sealed into a successful ElaborationFacts IS the [ep_tnft] of the phase actually built
   ([elaborate_ok_seals_tnfacts]) — quantified over the CONSTRUCTED object, not a global helper. *)
Print Assumptions GoCompile.facts_and_diags_share_phase.
Print Assumptions GoCompile.elaborate_ok_seals_tnfacts.
(* §8.1/§8.2/§9 THE DEPENDENT OBJECT CHAIN: the fact table is a [ForestExprFactTable] indexed by the exact
   forest/outcome table, carrying a proof its map IS the EOOk projection ([feft_is_facts]); the diagnostics are an
   [ExpressionDiagnostics] indexed by the exact retained [AnnotatedExprWorkForest] object and outcome table,
   carrying a proof its list IS the projection ([ed_is_diags]).  A foreign equal-map table / equal list is
   UNREPRESENTABLE — the dependent types encode the chain, not a provenance equality. *)
Print Assumptions GoCompile.feft_is_facts.
Print Assumptions GoCompile.ed_is_diags.
(* §11.2/§11.5 NO-RECONSTRUCTION SHARED OBJECT FLOW: each phase component IS the builder applied to the phase's OWN
   prior objects (definitional equality of the concrete [build_expression_phase] — one work-discovery let, passed
   forward; the sub-builders are forest/object-parameterized, so none re-runs [build_expr_work_forest]).  [ep_ot]
   consumed [ep_work]+[ep_tnft]; [ep_awork] consumed [ep_work]; [ep_eft] consumed [ep_work]+[ep_ot]; [ep_diag]
   consumed [ep_awork]+[ep_ot]. *)
Print Assumptions GoCompile.phase_ot_consumes_work.
Print Assumptions GoCompile.phase_awork_consumes_work.
Print Assumptions GoCompile.phase_eft_consumes_work_ot.
Print Assumptions GoCompile.phase_diag_consumes_awork_ot.
(* §9/§2.8 the fact-side seal by OBJECT IDENTITY: the ExprFactTable OBJECT sealed into a successful
   ElaborationFacts IS [feft_table (ep_eft)] of the phase actually built (not a fresh table whose map merely
   equals the projection). *)
Print Assumptions GoCompile.elaborate_ok_seals_facts.
(* §5/§2.9 the sealed type-name table has RETAINED-INPUT PROVENANCE: it IS build_type_name_fact_table of the
   phase's own CompilationInput — the phase's [ep_tnft] is DEFINITIONALLY that builder (no stored provenance
   equality; the concrete [build_expression_phase] let-binds it). *)
Print Assumptions GoCompile.elaborate_ok_seals_tnfacts_from_input.
(* §5.3 repeated equal source names at DISTINCT occurrences -> DISTINCT target refs (distinct keys) with EQUAL
   recovered syntax and EQUAL sealed facts (occurrence identity, not name identity) — the universal (conditional)
   property AND its CONCRETE non-hypothetical instance on a real compiled two-[uint8] program (the two occurrences
   and their real minted TypeNameRefs DISCHARGED from the source, not assumed). *)
Print Assumptions GoCompile.repeated_name_distinct_refs.
Print Assumptions GoCompile.two_uint8_distinct_target_refs.
(* §15/§10.8 the deep-nested conversion phase fixtures: a valid four-deep nest compiles and its TOTAL
   diagnostic projection is EMPTY (no fail-open); a deep nest with an innermost overflow yields EXACTLY ONE
   diagnostic (no drop, no per-ancestor double-count). *)
Print Assumptions GoCompile.deep_nested_compiles.
Print Assumptions GoCompile.deep_nested_no_diags.
Print Assumptions GoCompile.deep_fail_one_diag.
(* §12/§2.10 REAL PHASE fixtures: query [build_expression_phase]'s own [ep_diags] projection — a deep valid chain
   projects EMPTY, a deep inner failure REPORTS (non-empty, not suppressed). *)
Print Assumptions GoCompile.deep_nested_phase_no_diags.
Print Assumptions GoCompile.deep_fail_phase_reports.
(* §12 DIRECT PRODUCTION-OBJECT phase queries (NOT spec rewrites): a REAL [ExprWork] of the deep program's
   retained input is built and [total_forest_outcome_at] is queried on the phase's OWN [ep_ot] — the innermost
   int8(300) is the sole EOConvFail whose DIRECT cause reads the operand's stored EOOk (exact refs, no rescan);
   each enclosing conversion is EOChildFail; the stored diagnostic list is EXACTLY ONE; the valid deep chain's
   conversions + leaf all resolve EOOk; the retained work forest has EXACTLY 5 items; and the production table
   admits NO foreign key and NO wrong-kind (non-expression) key ([ep_work]/[ep_ot], not the specification). *)
(* §12/§6 the innermost convfail PROJECTS its RETAINED cause from the corrected outcome table: the member's
   [total_forest_outcome_cause] destructs to the exact insertion [StepCause], inverted to the exact [ConversionStep]
   whose operand outcome — read THROUGH the exact operand [SuffixMember] via [oa_total acc_rest] — is [EOOk opf],
   with ONE rejecting [convert_const] and an [EOConvFail] naming that exact operand ref. *)
Print Assumptions GoCompile.deep_fail_innermost_convfail.
Print Assumptions GoCompile.deep_fail_outer_childfail.
Print Assumptions GoCompile.deep_fail_exactly_one_diag.
Print Assumptions GoCompile.deep_nested_all_ok.
Print Assumptions GoCompile.deep_nested_seals_eft.
Print Assumptions GoCompile.deep_nested_work_count.
Print Assumptions GoCompile.phase_domain_exact.
(* §3/§4 (REPAIR 11) the DIRECT FINAL-TO-TAIL CLOSURE + STORED-DIAGNOSTIC evidence, gated as the accepted public
   surfaces — each accepted theorem STATES exactly the evidence its proof obtains:
   - the exact per-occurrence valid-chain SUCCESS bundle ([deep_nested_convsuccess_at], proving [nested_success_bundle]:
     current EConvert view + current final EOOk f + exact ConversionStep + operand SuffixMember + tail = final =
     EOOk opf + tail=final query equality + ONE convert_const success on the exact target fact + f the exact current
     ExprFact), and its instantiation on ALL FOUR valid conversions ([deep_nested_chain_success_evidence]);
   - the innermost convfail's retained cause CONNECTED to the exact stored [DRInvalidConversion]
     ([deep_fail_innermost_diag] — same fields, t = the exact predeclared-context target fact query
     [tnf_type (type_name_fact_at_table (ep_tnft phase) (cw_target_ref (cs_conversion step)))], the exact retained
     annotated member/context pair supplying [outer], and [ep_diags] EXACTLY that singleton, no second reason);
   - the strong per-occurrence child-failure closure ([deep_fail_childfail_closure_at]: exact ConversionStep +
     operand + tail=final failure + current EOChildFail + no local reason).
   The weaker projections are labeled COROLLARIES: [deep_nested_ok_closure_at] states only the operand tail/final
   EOOk + query equality (NO convert_const success / target fact / current fact); the concrete aggregates
   [deep_fail_outer_operands_final_fail], [deep_nested_chain_operands_final_ok], [deep_nested_all_ok] state only the
   outcome SHAPE. *)
Print Assumptions GoCompile.deep_nested_convsuccess_at.
Print Assumptions GoCompile.deep_nested_chain_success_evidence.
Print Assumptions GoCompile.deep_fail_innermost_diag.
Print Assumptions GoCompile.deep_fail_childfail_closure_at.
Print Assumptions GoCompile.deep_nested_ok_closure_at.
Print Assumptions GoCompile.deep_fail_outer_operands_final_fail.
Print Assumptions GoCompile.deep_nested_chain_operands_final_ok.
(* §4 the typed invalid-conversion reason DENOTES its code end-to-end (primary ExprRef, the exact minted target
   TypeNameRef, operand status, convert_const rejects); the erased report RETAINS the source target spelling so
   invalid byte(...) vs uint8(...) (and rune vs int32) — same resolved GoType — erase DISTINGUISHABLY. *)
Print Assumptions GoCompile.occ_expr_diags_conv_sound.
Print Assumptions GoCompile.byte_uint8_erased_differ.
Print Assumptions GoCompile.rune_int32_erased_differ.
(* the legacy compile class projects the elaboration diagnostics (matches the decision), not a rerun. *)
Print Assumptions GoCompile.go_compile_class_spec.
(* decision (expression half): every println argument resolves IFF program_typedb / ProgramTyped. *)
Print Assumptions GoCompile.expr_all_ok_program_typedb.
Print Assumptions GoCompile.expr_all_ok_ProgramTyped.
(* EXPRESSION COMPLETENESS: no expression diagnostic IFF the program types (the diagnostics<->decision
   equivalence for the expression half). *)
Print Assumptions GoCompile.emits_none_program_typedb.
Print Assumptions GoCompile.expr_diags_empty_iff.
(* PACKAGE COMPLETENESS + the retained ELABORATION ROOT: no package diagnostic IFF every package satisfies
   the factored rules; no diagnostic at all IFF the elaboration decision holds; and elaboration succeeds/fails
   IFF GoCompile/not. *)
Print Assumptions GoCompile.sum_main_file.
(* the PRODUCTION (retained-bucket) package decision captures EACH factored rule EXACTLY: the redeclaration
   diagnostics are empty IFF [PackageDeclsUnique], the missing-entry diagnostics IFF [MainPackagesHaveEntry], and
   all package diagnostics together IFF [PackageRulesValid] — rooted DIRECTLY in the factored roots, NOT the
   exactly-one consequence. *)
Print Assumptions GoCompile.redecl_diags_empty_iff_rules.
Print Assumptions GoCompile.missing_diags_empty_iff_rules.
(* [pkg_diags_empty_iff_rules] is the DIRECT factored-root surface; the older [pkg_diags_empty_iff] (empty IFF
   the exactly-one CONSEQUENCE) it supersedes stays an internal lemma, covered by the whole-theory audit. *)
Print Assumptions GoCompile.pkg_diags_empty_iff_rules.
Print Assumptions GoCompile.semantic_diagnostics_empty_iff.
Print Assumptions GoCompile.elaborate_ok_iff_GoCompile.
Print Assumptions GoCompile.elaborate_failed_iff_not_GoCompile.

(* the LIVE source root is the FACTORED [SourceProgramValid] (= ProgramTyped /\ PackageRulesValid,
   i.e. package-block uniqueness AND main-package entry as separate roots).  The retained universal theorem
   [current_package_rules_exactly_one] states the CURRENT-grammar consequence (the factored rules coincide with
   "every package has one main").  The DECIDABLE reflection is [source_spec_valid_b_iff] (and the decision-side
   [semantic_ok_b_SourceProgramValid], gated above) — DIRECT, with no [prog_ok]/[ProgValid]. *)
Print Assumptions GoCompile.current_package_rules_exactly_one.
(* the readable SPECIFICATION package reflection (for fixtures / proof convenience — NOT the production decision):
   [source_spec_package_rules_b] decides the two factored roots DIRECTLY (block uniqueness ↔ [PackageDeclsUnique],
   entry ↔ [MainPackagesHaveEntry]) — no combined "=1". *)
Print Assumptions GoCompile.source_spec_package_rules_b_PackageRulesValid.
Print Assumptions GoCompile.source_spec_valid_b_iff.
(* GoCompile INCLUDES the pinned one-shot `go build ./...` output PREFLIGHT.  The three
   diagnostic layers each have an emptiness/equivalence characterization (source, fresh, final); a failed
   preflight takes PRECEDENCE (exactly one build-output-directory diagnostic, hiding the sole package's semantic
   errors); go_compile only PROJECTS the one elaboration (no second checker). *)
Print Assumptions GoCompile.preflight_fails_iff.
Print Assumptions GoCompile.semantic_diagnostics_empty_iff_source_valid.
Print Assumptions GoCompile.fresh_build_diagnostics_nil_iff.
Print Assumptions GoCompile.fresh_build_diagnostics_fail_singleton.
Print Assumptions GoCompile.elaboration_diagnostics_nil_iff_GoCompile.
Print Assumptions GoCompile.elaboration_diagnostics_eq_semantic.
Print Assumptions GoCompile.elaboration_diagnostics_fresh_failure.
Print Assumptions GoCompile.go_compile_projects_elaborate.
(* the FreshBuildPlan / final report / acceptance class depend on the ModuleSpec (the preflight's
   default exec name is a ModulePath function), so their determinism needs the FULL ProgramInputEqual, NOT
   FilesEqual alone (the counterexample: equal files, different module -> different plan). *)
Print Assumptions GoCompile.root_layout_InputEqual.
Print Assumptions GoCompile.fresh_build_plan_InputEqual.
Print Assumptions GoCompile.erased_elaboration_report_InputEqual.
(* the fresh BUILD PLAN and ROOT LAYOUT are RETAINED in ElaborationFacts (derived ONCE from
   the retained package buckets, whose keys ARE the selected package set), so a CompilableProgram PROJECTS the
   exact plan its elaboration used — never a recompute from the program. *)
Print Assumptions GoCompile.bucket_keys_eq_selected.
Print Assumptions GoCompile.fresh_build_plan_of_buckets.
Print Assumptions GoCompile.cp_build_plan_retained.
Print Assumptions GoCompile.cp_root_layout_retained.
(* the COMPLETE fresh-root-layout EXACTNESS: the "go.mod"->FREGoMod entry (and it is the ONLY
   FREGoMod key); a key maps to FRESourceFile IFF a root-level file has it; the DIRECTORY characterization
   (existing [root_layout_dir_iff]); and the whole no-extra-entry DOMAIN — plus the disjointness underpinning
   ([root_entry_hval] / [root_entry_key_neq_gomod]). *)
Print Assumptions GoCompile.root_entry_key_neq_gomod.
Print Assumptions GoCompile.root_entry_hval.
Print Assumptions GoCompile.root_layout_dir_iff.
Print Assumptions GoCompile.root_layout_gomod.
Print Assumptions GoCompile.root_layout_gomod_iff.
Print Assumptions GoCompile.root_layout_source_iff.
Print Assumptions GoCompile.root_layout_domain.
(* the UNIVERSAL package-selection / import-path / executable-name / plan exactness (not just
   computed fixtures): visibility (a selected key IS a represented file's parent); the import-path INJECTIVITY
   in the package directory and its determinism (the directory key is recovered EXACTLY through the component
   authority) plus the nested string form; the NEVER-EMPTY default executable name, proved over the import
   path's COMPONENT LIST; the exact zero/single/multiple plan classification and the sole-main plan's stored
   output target. *)
Print Assumptions GoCompile.selected_iff_file.
Print Assumptions GoCompile.selected_key_is_parent.
Print Assumptions GoCompile.package_import_path_nested.
Print Assumptions GoCompile.package_import_path_inj.
Print Assumptions GoCompile.package_import_path_deterministic.
Print Assumptions GoCompile.default_exec_name_nonempty.
Print Assumptions GoCompile.fresh_build_plan_exec_nonempty.
Print Assumptions GoCompile.fresh_build_plan_zero.
Print Assumptions GoCompile.fresh_build_plan_multiple.
Print Assumptions GoCompile.fresh_build_plan_single_target.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree; a resolved expression evaluates
   to a well-formed value of the resolved GoType (one type authority across compiler and runtime); value
   well-formedness reflection; an explicit INTEGER conversion carries its exact converted value (a float
   conversion rounds once); a string literal evaluates to the EXACT runtime byte sequence of its resolved
   type. *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.
Print Assumptions GoSafe.eval_expr_resolved.
Print Assumptions GoSafe.eval_expr_resolved_type.
(* evaluation returns EXACTLY the resolved typed constant's stored value — a resolved float projects its
   packaged tfc_runtime (no second round), stated generically and as the explicit float-runtime corollary. *)
Print Assumptions GoSafe.resolved_const_value_float.
Print Assumptions GoSafe.eval_expr_resolved_value.
Print Assumptions GoSafe.eval_projects_stored_float_runtime.
Print Assumptions GoSafe.value_wfb_iff.
Print Assumptions GoSafe.typed_const_to_value_denotes.
Print Assumptions GoSafe.eval_string_value.
Print Assumptions GoSafe.eval_string_resolved_type.
(* complex runtime: the typed-complex projection preserves type; a typed-complex runtime denotes its exact
   typed complex constant; a NaN / infinity / negative-zero component runtime value denotes NO constant;
   evaluation returns EXACTLY the stored typed_complex_runtime. *)
Print Assumptions GoSafe.typed_const_to_value_complex.
Print Assumptions GoSafe.value_denotes_complex_runtime.
Print Assumptions GoSafe.eval_projects_stored_complex_runtime.

(* GoRender: all output ASCII (including conversions); the ONE ConstInfo render-status root
   (render_const_info_denotes: rendering denotes exactly the const_info GoTypes computes) which is FUNCTIONAL
   (render_const_info_denotes_functional: a rendered spelling denotes at most ONE ConstInfo — the bool / bare
   integer / string / integer-conversion / bare float / float-conversion / complex-literal / complex-conversion
   recognisers are pairwise disjoint (and `complex(` is distinct from `complex64(`/`complex128(` at index 7), so
   no spelling admits two conflicting constant statuses) and the final
   resolved root (resolved argument -> const-status + well-formed value of its resolved type carrying the same
   constant); the integer-repair regressions (a bare integer above int_max stays UNTYPED, does NOT denote a
   typed int, and only an explicit uint64 conversion assigns the type); the ten integer keywords are ASCII;
   the exact conversion spellings; decimal faithfulness + no leading zero; int boundaries; the header is the
   EXACT first line of a .go file; go.mod is rendered from the ModuleSpec — exact bytes, header first line,
   all ASCII. *)
Print Assumptions GoRender.render_file_ascii.
(* the import domain is INTRINSICALLY empty and the renderer STRUCTURALLY consumes [source_imports], so a
   future import constructor forces a renderer update rather than being silently dropped. *)
Print Assumptions GoRender.source_imports_nil.
Print Assumptions GoRender.render_imports_nil_bytes.
Print Assumptions GoRender.render_expr_ascii.
Print Assumptions GoRender.render_const_info_denotes.
Print Assumptions GoRender.render_const_info_denotes_functional.
Print Assumptions GoRender.render_resolved_expr_denotes.
(* §11 the source type name is rendered from the RETAINED source identifier: distinct conversion type names
   render distinct text, so the byte/rune source aliases render "byte"/"rune" — distinct from "uint8"/"int32"
   even though they resolve to equal semantic types. *)
Print Assumptions GoRender.render_type_syntax_inj.
Print Assumptions GoRender.render_conv_byte_neq_uint8.
Print Assumptions GoRender.render_conv_rune_neq_int32.
(* float rendering: the canonical decimal spelling + conversion spellings; ASCII; the decoder/renderer
   semantic round trip; a bare float denotes its exact rational, a conversion the rounded typed constant. *)
Print Assumptions GoRender.render_decimal_ascii.
Print Assumptions GoRender.decode_render_decimal.
Print Assumptions GoRender.render_float_denotes.
Print Assumptions GoRender.print_Z_dec_faithful.
Print Assumptions GoRender.print_Z_pos_no_leading_zero.
Print Assumptions GoRender.render_boundary_max.
Print Assumptions GoRender.render_boundary_min.
Print Assumptions GoRender.render_file_first_line.
Print Assumptions GoRender.render_go_mod_exact.
Print Assumptions GoRender.render_go_mod_first_line.
Print Assumptions GoRender.render_go_mod_ascii.
(* strings: the encoder/decoder round trip (an INDEPENDENT decoder inverts the canonical encoder); the
   rendered literal is all-ASCII even for bytes >= 128 and contains no raw newline/CR (quoting shape); every
   `\xhh` byte round-trips exactly (hex exactness); a boundary-byte escape spelling is pinned exactly *)
Print Assumptions GoRender.render_string_roundtrip.
Print Assumptions GoRender.render_string_literal_ascii.
Print Assumptions GoRender.render_string_literal_no_nl_cr.
Print Assumptions GoRender.render_hex_escape_exact.
Print Assumptions GoRender.render_string_denotes.
Print Assumptions GoRender.render_resolved_string_denotes.
(* complex rendering: the exact complex64/complex128 keywords are ASCII; the canonical complex(real, imag)
   literal renders exactly and is ASCII; the INDEPENDENT complex decoder round-trips the canonical spelling
  ; the conversion spellings; a bare complex literal denotes its exact ComplexConst (the FUNCTIONAL
   denotation + final resolved root, gated generically above, now cover complex too). *)
Print Assumptions GoRender.render_complex_literal_ascii.
Print Assumptions GoRender.decode_render_complex_literal.
Print Assumptions GoRender.render_cplx_denotes.

(* GoEmit: the public emitter requires SafeProgram; the complete image is go.mod + the (possibly empty)
   .go map; the go.mod and every .go file begin with the header first line and are ASCII; on-disk .go
   paths are unique (duplicate paths impossible).  NO nonemptiness claim — the empty program is valid. *)
Print Assumptions GoEmit.render_program_go_mod_header.
Print Assumptions GoEmit.render_program_go_mod_ascii.
Print Assumptions GoEmit.render_program_header.
Print Assumptions GoEmit.render_program_ascii.
Print Assumptions GoEmit.render_image_keys_nodup.
(* rendering over the standard file map: the rendered map has the SAME key domain as the source; every
   binding is EXACTLY [render_file] of its source; [FilesEqual] sources render to [FM.Equal] maps whose
   CANONICAL transport lists are EQUAL; and the whole [di_transport] is INDEPENDENT of input-node order. *)
Print Assumptions GoEmit.render_map_domain.
Print Assumptions GoEmit.render_map_binding.
Print Assumptions GoEmit.render_map_Equal.
Print Assumptions GoEmit.di_go_file_entries_Equal.
Print Assumptions GoEmit.di_transport_order_independent.
(* the DirectoryImage BRIDGE: the rendered image REALIZES the fresh root layout the plan is
   computed over ([image_source_layout] over the image's own keys = [root_layout] over the source program), and
   its `.go` file keys are EXACTLY the source FilePaths (no extra entry; go.mod is a distinguished field). *)
Print Assumptions GoEmit.directory_image_realizes_fresh_layout.
Print Assumptions GoEmit.image_go_files_are_source_paths.
(* the RETAINED-PLAN / IMAGE bridge: a rendered image realizes the CompilableProgram's RETAINED
   root layout ([ef_root_layout]) AND the retained build plan's output-target classification is the ACTUAL
   image's classification at that output name — the collision check is against the real emitted tree. *)
Print Assumptions GoEmit.directory_image_realizes_retained_layout.
Print Assumptions GoEmit.image_output_target_of_retained_plan.

(* GoIndex (Source Forest): the PRODUCTION occurrence index over the ONE raw GoProgram grammar — Pillar 1
   (source/index exactness).  The sealed standard positive-key node-table laws; the per-file occurrence-count
   equals the table-free boundary function; and the load-bearing UNIVERSAL per-file source/index exactness
   theorem — the metadata the one-pass builder stores at every local id is EXACTLY the metadata of the exact
   source occurrence there (kind/role/parent/subtree, presence AND absence), against an INDEPENDENT table-free,
   builder-independent source-occurrence specification over the real grammar (file root / package clause /
   declarations / statements / println arguments / conversion operands) — plus its consequences (A..H). *)
Print Assumptions GoIndex.NodeTable.get_empty.
Print Assumptions GoIndex.NodeTable.get_set_same.
Print Assumptions GoIndex.NodeTable.get_set_other.
Print Assumptions GoIndex.build_file_count.
Print Assumptions GoIndex.build_file_source_exact.
Print Assumptions GoIndex.source_occurrence_meta.
Print Assumptions GoIndex.meta_source_occurrence.
Print Assumptions GoIndex.source_absence.
Print Assumptions GoIndex.source_occurrence_unique.
Print Assumptions GoIndex.source_kind_exact.
Print Assumptions GoIndex.source_role_exact.
Print Assumptions GoIndex.source_parent_exact.
Print Assumptions GoIndex.source_subtree_end_exact.
(* GoIndex Pillar 2 — the structural navigation invariants over the built per-file index: the file index is
   well-formed; root id canonical / no parent, only the root has no parent, every non-root has a unique
   parent; the interval-jump direct-child enumeration is sound + complete (parent/child inverse) and source-
   ordered; the O(1) preorder-interval ancestor test is sound + complete; canonical enumeration is
   sound/complete/NoDup; the builder branches only on SHAPE (no structural-equality dedup); metadata stores no
   subtree copy. *)
Print Assumptions GoIndex.build_file_wf.
Print Assumptions GoIndex.thm1_root_id_canonical.
Print Assumptions GoIndex.thm2_root_no_parent.
Print Assumptions GoIndex.thm3_nonroot_has_parent.
Print Assumptions GoIndex.thm3b_parent_unique.
Print Assumptions GoIndex.first_child.
Print Assumptions GoIndex.next_child.
Print Assumptions GoIndex.child_enum.
Print Assumptions GoIndex.child_enum_sound.
Print Assumptions GoIndex.child_enum_reaches.
Print Assumptions GoIndex.thm4_child_has_parent.
Print Assumptions GoIndex.thm4_parent_has_child.
Print Assumptions GoIndex.thm11_children_sorted.
Print Assumptions GoIndex.anc_complete.
Print Assumptions GoIndex.thm13_interval_ancestry.
Print Assumptions GoIndex.thm7_enum_nodup.
Print Assumptions GoIndex.thm7_enum_complete.
Print Assumptions GoIndex.thm7_enum_sound.
Print Assumptions GoIndex.thm_builder_no_structural_search.
Print Assumptions GoIndex.thm14_meta_stores_no_subtree.
(* GoIndex Pillar 3 — the SEALED reference layer indexed by the exact GoProgram: decidable NodeKey identity;
   the sealed Snap API (index_program / file_of_path / ref_of_key / total ref_meta/kind/role/subtree/
   containing_file/parent_of/children_of/node_at/source_occurrence_of_ref/is_ancestor_ref) whose raw
   constructors are hidden; reference/file extensionality + NodeKey injectivity; total navigation (root has no
   parent / only root / parent same file / children same file / parent-child inverse both ways / source-ordered
   NoDup children / ref-level ancestry sound+complete); minting sound + complete + non-circular source
   membership; and the EXACT source-occurrence correspondence lifted through the sealed API (metadata / kind /
   role / parent / subtree / source view all pinned to the exact source occurrence). *)
Print Assumptions GoIndex.thm8_nodekey_eq_dec.
Print Assumptions GoIndex.thm8_nodekey_eqb_spec.
(* outer-index exactness: the derived outer index [outer_of] (which the sealed [SyntaxIndex]'s internal
   map IS) holds, at every path, EXACTLY the per-file build of the program's file there and nothing at a path
   with no file — presence AND absence, so no entry can belong to another snapshot and none is spurious. *)
Print Assumptions GoIndex.outer_get_exact.
Print Assumptions GoIndex.Snap.index_program.
Print Assumptions GoIndex.Snap.file_of_path.
Print Assumptions GoIndex.Snap.ref_of_key.
Print Assumptions GoIndex.Snap.ref_meta.
Print Assumptions GoIndex.Snap.node_kind.
Print Assumptions GoIndex.Snap.parent_of.
Print Assumptions GoIndex.Snap.children_of.
Print Assumptions GoIndex.Snap.node_at.
Print Assumptions GoIndex.Snap.source_occurrence_of_ref.
Print Assumptions GoIndex.Snap.node_ref_ext.
Print Assumptions GoIndex.Snap.thm_node_kind.
Print Assumptions GoIndex.Snap.thm_node_role.
Print Assumptions GoIndex.Snap.thm_ref_meta_built.
Print Assumptions GoIndex.Snap.thm_containing_file.
Print Assumptions GoIndex.Snap.node_ref_key_inj.
Print Assumptions GoIndex.Snap.file_ref_path_inj.
Print Assumptions GoIndex.Snap.thm_parent_root.
Print Assumptions GoIndex.Snap.thm_parent_nonroot.
Print Assumptions GoIndex.Snap.thm_parent_same_file.
Print Assumptions GoIndex.Snap.thm_children_same_file.
Print Assumptions GoIndex.Snap.thm_child_parent.
Print Assumptions GoIndex.Snap.thm_parent_child.
Print Assumptions GoIndex.Snap.thm_children_of_source_order.
Print Assumptions GoIndex.Snap.thm_children_of_nodup.
Print Assumptions GoIndex.Snap.ref_of_key_sound.
Print Assumptions GoIndex.Snap.ref_of_key_complete.
Print Assumptions GoIndex.Snap.file_of_path_complete.
Print Assumptions GoIndex.Snap.file_of_path_source.
Print Assumptions GoIndex.Snap.ref_of_key_source.
Print Assumptions GoIndex.Snap.is_ancestor_ref.
Print Assumptions GoIndex.Snap.thm_ref_ancestry.
Print Assumptions GoIndex.Snap.ref_meta_matches_source.
Print Assumptions GoIndex.Snap.node_kind_matches_source.
Print Assumptions GoIndex.Snap.node_role_matches_source.
Print Assumptions GoIndex.Snap.node_parent_matches_source.
Print Assumptions GoIndex.Snap.node_subtree_end_matches_source.
Print Assumptions GoIndex.Snap.source_occ_of_ref_eq.
Print Assumptions GoIndex.Snap.node_at_matches_source_view.
Print Assumptions GoIndex.Snap.node_parent_ref_matches_source.
(* GoIndex typed/kind-refined references: the kind-refiner is sound + complete + mismatch-rejecting, the
   refined kind is the EXACT source occurrence's kind (not a free boolean), and the erased NodeKey determines
   the typed-reference identity. *)
Print Assumptions GoIndex.erase_as_kind.
Print Assumptions GoIndex.as_kind_complete.
Print Assumptions GoIndex.as_kind_mismatch.
Print Assumptions GoIndex.noderefof_kind.
Print Assumptions GoIndex.noderefof_key_inj.
(* GoIndex ROOT-completeness surfaces: FileRef minting soundness + the invalid-path /
   invalid-local rejection cases; decidable NodeRef equality; and the CANONICAL preorder enumeration of ALL a
   file's references (same-file / complete / NoDup / source-ordered) with reachability of every occurrence from
   its file root by repeated parent links. *)
Print Assumptions GoIndex.Snap.file_of_path_sound.
Print Assumptions GoIndex.Snap.file_of_path_source_exact.
Print Assumptions GoIndex.Snap.ref_of_key_invalid_path.
Print Assumptions GoIndex.Snap.ref_of_key_invalid_local.
Print Assumptions GoIndex.Snap.noderef_eq_dec.
Print Assumptions GoIndex.Snap.file_root_ref_local.
Print Assumptions GoIndex.Snap.file_root_ref_file.
Print Assumptions GoIndex.Snap.file_refs_same_file.
Print Assumptions GoIndex.Snap.file_refs_complete.
Print Assumptions GoIndex.Snap.file_refs_nodup.
Print Assumptions GoIndex.Snap.file_refs_source_order.
Print Assumptions GoIndex.Snap.file_root_ref_in_refs.
Print Assumptions GoIndex.Snap.thm_reachable_from_root.
Print Assumptions GoIndex.Snap.thm_refs_reachable.
(* the canonical INDEXED TRAVERSAL: the structural one-pass occurrence fold is EXACT (lists exactly the
   graph of source_occurrence_at) and canonically ORDERED; lifted to the reference level, [visit_file] supplies
   each occurrence's validated NodeRef paired with its ORIGINAL syntax view TOGETHER — exact, same-file,
   complete over the file, in canonical source preorder order, NoDup (no per-node source recovery). *)
Print Assumptions GoIndex.occs_file_exact.
Print Assumptions GoIndex.occs_file_sorted.
Print Assumptions GoIndex.Snap.visit_file_view.
Print Assumptions GoIndex.Snap.visit_file_complete.
Print Assumptions GoIndex.Snap.visit_file_order.
Print Assumptions GoIndex.Snap.visit_file_nodup.
Print Assumptions GoIndex.Snap.node_ref_key_eq.
(* support: [view_expr] is Some exactly for a KExpression occurrence (the dependent SyntaxView). *)
Print Assumptions GoIndex.view_expr_kind.
Print Assumptions GoIndex.kind_view_expr.
(* the retained IndexedProgram phase boundary: canonical construction reuses exactly the one
   Snap.index_program, and the retained index is the projected field. *)
Print Assumptions GoIndex.index_program_syntax.
Print Assumptions GoIndex.indexed_syntax_proj.
(* the canonical NodeKey ordered key + standard AVL map: ordered equality, add/find laws, and canonical
   elements as a function of the map's meaning (Equal maps enumerate identically). *)
Print Assumptions GoIndex.nodekey_compare_eq.
Print Assumptions GoIndex.nodekeymap_add_eq.
Print Assumptions GoIndex.nodekeymap_add_neq.
Print Assumptions GoIndex.nodekeymap_elements_Equal.
(* the UNIVERSAL query-projection bridge: every typed expression query PROJECTS its occurrence's
   EXACT analyzed fact (the const-status the fact table stores).  (The concrete per-program erased-report /
   fact-enumeration / single-failure-scar fixtures stay COMPILED as tests + covered by the whole-theory audit,
   but are NOT gated surfaces — they are fixed-program witnesses, not universal claims.) *)
Print Assumptions GoCompile.expr_fact_at_exact.
(* the UNIVERSAL STRICT canonical-order theorem: the report's node-primary diagnostics appear in
   STRICTLY ascending NodeKey order (path then local id) via the standard NodeKeyMap's key-sorted elements —
   NO project-authored sort.  Backed by the two supporting claims the order rests on: the node-keyed INPUT has
   UNIQUE keys (expr keys NoDup + pkg keys NoDup + their disjointness), so every bucket is a SINGLETON — hence
   there are NO within-bucket ties to reorder; the bucketing is a REORDERING and the report has exactly the
   diagnostics of `expr_diags ++ pkg_diags`. *)
Print Assumptions GoCompile.collect_node_input_nodup.
Print Assumptions GoCompile.collect_node_buckets_singleton.
Print Assumptions GoCompile.semantic_diagnostics_node_strict.
Print Assumptions GoCompile.collect_diagnostics_In.
(* the SOURCE characterization of the erased report (ties the report to its source form; the universal
   diagnostic-exactness claims above rest on it). *)
Print Assumptions GoCompile.erased_report_src_eq.
