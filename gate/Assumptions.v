(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    program-rooted Syntax.Program -> Typing (the one type authority: untyped Typing.Constant resolved through
    {Typing.BoolType, the integer family Typing.IntegerType over Integer.Kind, the float family Typing.FloatType over Float.Kind, the complex
    family Typing.ComplexType over Complex.Kind, Typing.StringType} to
    Typing.Program over the same AST) ->
    Admissible -> Property -> Render -> Emit architecture. *)
From Fido Require Import Integer Float Complex FilePath Collections ModulePath Version Syntax Index Typing Compilable Safe Render Emit.

(* the ONE integer-family authority: type-equality reflection; the single representability reflection;
   exact 64-bit int/uint; generic min/max accepted and below-min/above-max rejected;
   int<>int64 and uint<>uint64 distinct despite equal ranges; the derived default-int bounds. *)
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

(* the ONE float-family authority (Float.v, axiom-free over SpecFloat): Float.Kind equality;
   precision/exponent settings; direct binary32/binary64 rounding of exact rationals; the double-rounding
   counterexample (direct F32 differs from binary64-then-binary32); precision boundaries 2^24+1 / 2^53+1. *)
Print Assumptions Float.kind_equalb_spec.
Print Assumptions Float.precision_f32.
Print Assumptions Float.precision_f64.
Print Assumptions Float.maximum_exponent_f32.
Print Assumptions Float.maximum_exponent_f64.
(* exact-rational canonicality + equality: every Float.Constant is INTRINSICALLY canonical (coprime by the record's
   own well-formedness field), so it is fixed by its numerator/denominator (Float.numerator_denominator_eq) and reflected equality
   IS Leibniz equality (Float.constant_equalb_eq); cross-multiplication decides value equality; reduction yields a coprime form
   of the same value; on canonical forms value equality IS Leibniz equality (lowest terms). *)
Print Assumptions Float.constant_canonical_intrinsic.
Print Assumptions Float.numerator_denominator_eq.
Print Assumptions Float.constant_equalb_eq.
Print Assumptions Float.constant_equalb_spec.
Print Assumptions Float.constant_of_Z_canonical.
Print Assumptions Float.reduce_constant_canonical.
Print Assumptions Float.reduce_constant_eq.
Print Assumptions Float.constant_canonical_unique.
(* the ONE constant-conversion/representability authority: reflected decision; the double-round scar back as
   an exact integer constant; overflow rejects; underflow rounds to canonical +0; a source zero -> +0. *)
Print Assumptions Float.representableb_spec.
(* the intrinsic finite-decimal raw literal domain: equality by canonical representation (proof-irrelevant
   well-formedness); the exact rational value is canonical; the unique (0,0) zero -> unsigned zero; a bound /
   non-canonical fixture rejects. *)
Print Assumptions Float.decimal_equalb_spec.
Print Assumptions Float.decimal_value_canonical.
Print Assumptions Float.decimal_value_zero.
Print Assumptions Float.decimal_zero_unique.
(* the runtime float value's format-canonical invariant: an unsigned-zero constant rounds to +0, never -0
   (representability reflection [Float.representableb_spec] is gated once, above). *)
Print Assumptions Float.round_ieee_zero.
Print Assumptions Typing.convert_constant_same_int.
Print Assumptions Typing.typed_int_value.
(* a constant NEVER evaluates to negative zero (the bare-negative-underflow scar): the constructed runtime
   value strips the sign of a zero, so it is never -0. *)
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

(* Complex — the ONE complex-type authority, COMPOSED from the Float component authority: decidable
   Complex.Kind equality; the ONE component mapping (C64->F32, C128->F64) sourcing all
   precision; exact Complex.Constant equality; the decimal-complex exact value projections; Complex.round_typed's
   componentwise results (each rounds ONCE) + representability reflection + component-overflow rejection;
   underflow-to-+0 + no-NaN/Inf/-0 runtime component shape (inherited from Float.TypedConstant); the runtime
   component read-back coherence. *)
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

(* intrinsic FilePath.T: decidable equality; a representable canonical path; a rejected (unrepresentable)
   path.  Non-canonical paths have no FilePath.T value at all — this is unrepresentability, not rejection. *)
Print Assumptions FilePath.equalb_spec.

(* intrinsic ModulePath.T: decidable equality; a representable canonical module path; rejected
   (unrepresentable) module paths.  Invalid module paths have no ModulePath.T value at all. *)
Print Assumptions ModulePath.equalb_spec.

(* intrinsic Version: the singleton Go1_23 renders EXACTLY "1.23"; decidable equality *)
Print Assumptions Version.render_go1_23.
Print Assumptions Version.equalb_spec.

(* the ONE standard-collection foundation: the [FilePath.T] ordered key and the standard AVL/positive
   map wrappers are backed by pinned rocq-stdlib [FMapAVL]/[FMapPositive] — Fido authors no map/set.  The
   [FilePath.T] ordered-type law ([Collections.file_path_text_inj]) that keys the standard file map is axiom-free, and the sorted
   AVL [elements] of extensionally-equal maps are the SAME canonical list ([Collections.file_elements_equal]). *)
Print Assumptions Collections.file_path_text_inj.
Print Assumptions Collections.file_elements_equal.

(* Typing — the ONE type authority (EVIDENCE over the raw AST): zero-sign constant equality; default-type
   exactness (int / FLOAT->float64); representability reflection; the constant-status analysis [Typing.constant_info]
   carries the exact value via [Typing.constant_info_exact], routed through the ONE [Typing.convert_constant] into an intrinsic
   [Typing.TypedConstant]/[Typing.ResolvedConstant] + a representable typed integer value; resolution sound + complete +
   deterministic; statement + program typing reflection. *)
Print Assumptions Typing.constant_info_zero_sign.
Print Assumptions Typing.constant_representableb_iff.
Print Assumptions Typing.resolve_sound.
Print Assumptions Typing.resolve_complete.
Print Assumptions Typing.resolve_deterministic.
Print Assumptions Typing.stmt_typedb_iff.
Print Assumptions Typing.program_typedb_iff.
(* map-based typing is ORDER-INDEPENDENT: it respects semantic map equality (as a Prop and reflected as a
   bool) and is therefore invariant under reordered [build_program] construction. *)
Print Assumptions Typing.program_equal.
Print Assumptions Typing.program_typedb_equal.
Print Assumptions Typing.program_typedb_build_permutation.
(* the per-occurrence typing predicate folded over the canonical source occurrence stream equals the
   existing [source_file_typedb].  This occurrence/traversal bridge lives in Admissible (the sole Index+Typing
   meeting point); Typing owns the type/constant relation only and imports no Index. *)
Print Assumptions Compilable.occurrences_file_typedb_eq.
(* the one-node semantic step: [Typing.constant_info] reflects [Typing.constant_info_step] applied to its child's status
   (the reusable one-pass leaf authority; Typing.convert_constant stays the sole conversion authority). *)
Print Assumptions Typing.constant_info_step_reflect.
(* the string-representability reflections (cross-kind non-resolution): EVERY string constant is representable
   as Typing.StringType, and no string constant is representable as an integer. *)
Print Assumptions Typing.string_representable.
Print Assumptions Typing.string_representableb.
(* the constant-conversion reflections AT USE (Typing.convert_constant the sole conversion authority): an untyped
   int / float / complex constant types through Typing.convert_constant (type_untyped_*_convert); a same-type complex
   conversion is the identity (Typing.convert_constant_same_complex, the universal exact-value erasure); a
   matching-format typed float REUSES the complex real component and a typed complex PROJECTS to that scalar
   float (convert_*_reuses_*_component). *)
Print Assumptions Typing.convert_constant_same_complex.
Print Assumptions Typing.convert_complex_reuses_float_component.
Print Assumptions Typing.convert_float_reuses_complex_component.
Print Assumptions Typing.type_untyped_int_convert.
Print Assumptions Typing.type_untyped_float_convert.
Print Assumptions Typing.type_untyped_complex_convert.

(* the map-backed SOURCE FOREST — [Syntax.Program]'s files are a STANDARD FilePath.T map ([Syntax.Files]).  The
   duplicate-rejecting builder [Syntax.files_of_nodes] is SOUND and COMPLETE (success iff the node paths are
   unique; failure iff a path repeats), its domain is exactly the input paths, and — the EXACTNESS pair — on
   success every input node maps to ITS OWN source ([Syntax.files_of_nodes_maps_to]; a duplicate FAILS the build,
   it never silently overwrites) and every built binding comes from an input node
   ([Syntax.files_of_nodes_mapsto_source]).  The semantic file-map equality is an equivalence.  ONE path authority
   (the map key); [Syntax.FileNode] is construction/view only. *)
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

(* Admissible (A) internal exactness: the executable source decision reflects the LIVE factored source root
   [SourceProgramValid]; Compilable.compile sound + complete against it; a rejected program yields no
   Compilable.Program; the compiled evidence exposes that the same program is typed; the empty program is
   accepted; a concrete integer-family program compiles; an out-of-range and an invalid-nested-conversion
   program are rejected with the honest typing error (and have no Compilable.Program); a concrete string
   program compiles. *)
Print Assumptions Compilable.semantic_ok_b_source_program_valid.
Print Assumptions Compilable.compile_ok_valid.
Print Assumptions Compilable.compile_complete.
(* PROVENANCE + RETENTION: every Compilable.Program's facts ARE elaborate's exact accepted core
   (no parallel capability path), and it RETAINS the exact elaborated index (the projection retains, never
   reconstructs). *)
Print Assumptions Compilable.compilable_retains_phase.
Print Assumptions Compilable.compilable_retains_expr_facts.
Print Assumptions Compilable.compilable_retains_tnfacts.
Print Assumptions Compilable.program_of_admissible.
Print Assumptions Compilable.capability_source.
Print Assumptions Compilable.capability_is_compile_outcome.
Print Assumptions Compilable.compile_rejected_not_admissible.
(* §3 THE SEALED IMAGE: the representation and its constructor are private (Charter §22/§24), so the image
   RETAINS the exact certificate it was minted from and provenance is a PROJECTION of that certificate rather
   than an existential a caller supplied.  Constructor inaccessibility is not a Print-Assumptions surface —
   it is enforced by the negative client tests Y-AB in `make prove`. *)
Print Assumptions Emit.image_safe.
Print Assumptions Emit.module_bytes_exact.
Print Assumptions Emit.files_exact.
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
(* map-based PACKAGE GROUPING via a standard [PackageMap] in ONE [FileMap.fold]: EXACTNESS (every file
   contributes to its own parent package; no package without a file; a summary's main count IS the sum over
   its files; empty file map -> empty package map) and ORDER-INDEPENDENCE (map-equal file collections and
   permuted construction yield map-equal package summaries, so [Admissible]/[Compilable.compile]'s accept-or-error
   class is invariant under file insertion order). *)
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
(* PackageRef: a validated package-key absence anchor.  Key identity determines the ref (UIP over the
   boolean membership proof), the key names a represented package, and construction from a binding / file
   reference yields the right key. *)
Print Assumptions Compilable.package_ref_present.
Print Assumptions Compilable.package_ref_key_inj.
Print Assumptions Compilable.package_ref_of_binding_key.
Print Assumptions Compilable.package_ref_of_fileref_key.
(* structured diagnostic core: the primary anchor is an exact-snapshot handle whose kind matches the
   reason's code (invalid anchor/category combinations are unrepresentable). *)
Print Assumptions Compilable.diagnostic_code_primary_consistent.
(* END-TO-END diagnostic soundness (each diagnostic DENOTES its reported code): an invalid-conversion
   diagnostic's primary is the occurrence's OWN ExprRef, its syntax IS the explicit conversion to the reported
   target of some operand x, the reported operand status is x's exact Typing.ConstantInfo, and [Typing.convert_constant] genuinely
   REJECTS it; a default-not-representable diagnostic is a genuine println argument whose exact untyped constant
   does NOT default and whose target is exactly the Go default; a missing-main (whole report) anchors a
   REPRESENTED package that genuinely contains ZERO Syntax.Main declarations; a duplicate-main relates a bucket-tail
   main to the FIRST-in-bucket main, both genuine top-level (func main) declarations in the SAME package. *)
Print Assumptions Compilable.occurrence_expr_diags_conv_sound.
Print Assumptions Compilable.occurrence_expr_diags_default_sound.
(* the NESTED SCAR: every enclosing-conversion (outer_context) ref of an invalid-conversion diagnostic
   in the whole expression report is a genuine CONVERSION whose subtree STRICTLY contains the primary (a real
   strict-ancestor conversion — node_ref_local < primary <= node_subtree_end), and the outer_context is
   SAME-FILE (as the primary), NEAREST-FIRST (deepest enclosing conversion first), and DUPLICATE-FREE (NoDup);
   delivered by the one-pass annotation and proved sound; never fabricated or copied syntax. *)
Print Assumptions Compilable.annotate_program_ctx_sound.
Print Assumptions Compilable.annotate_program_ctx_wf.
Print Assumptions Compilable.expression_diags_conversion_single_rounding_sound.
Print Assumptions Compilable.expression_diags_conversion_single_rounding_well_formed.
Print Assumptions Compilable.package_diag_of_bucket_missing_sound.
Print Assumptions Compilable.package_diag_of_bucket_dup_sound.
Print Assumptions Compilable.package_diags_dup_sound.
Print Assumptions Compilable.package_diags_dup_precedence.
Print Assumptions Compilable.package_diags_missing_sound.
(* cross-snapshot determinism FOUNDATION: the KEYED visit stream (each visited reference's Index.Key
   + its source occurrence) depends ONLY on the file map, so FilesEqual programs have IDENTICAL keyed streams
   (the basis for equal erased reports / fact enumerations). *)
Print Assumptions Compilable.keyed_visit_files_equal.
(* THE cross-snapshot determinism theorem: two programs with the SAME file map (whose diagnostics
   live in DIFFERENT dependent snapshot types) produce the IDENTICAL erased report — it depends ONLY on the
   file map, never on the snapshot index or the backing AVL shape.  The expression half factors through
   [annotate_source] (the one-pass enclosing context erases to a source function of the keyed stream); the
   package half through the keyed source buckets ([Compilable.program_package_erased_find] + PackageMap canonical elements). *)
Print Assumptions Compilable.annotate_encl_erased.
Print Assumptions Compilable.program_package_erased_find.
Print Assumptions Compilable.erased_expr_diags_source.
Print Assumptions Compilable.erased_pkg_diags_files_equal.
Print Assumptions Compilable.erased_report_files_equal.
(* the erased build-OUTPUT NAME payload: [Compilable.diagnostic_output] is the reason's exact planned output name
   for a build-output-directory reason and none elsewhere; the erased fresh report of a sole colliding package
   CARRIES that name (so cross-snapshot comparison distinguishes different collision names); concrete "a". *)
Print Assumptions Compilable.erase_diagnostic_output.
Print Assumptions Compilable.erased_output_iff_build_output.
Print Assumptions Compilable.erased_fresh_report_of_sole.
(* construction-permutation corollary: building the same module from a PERMUTED file-node list
   yields the IDENTICAL erased report (the report is invariant to the proposer's file order). *)
Print Assumptions Compilable.erased_report_build_permutation.
(* SUCCESSFUL-fact enumeration determinism: the expression fact Index.table depends ONLY on the
   file map (source NodeKeys + source-derived values, a fold-map fusion over the keyed stream), so FilesEqual
   programs have the IDENTICAL canonical fact enumeration. *)
Print Assumptions Compilable.program_expr_facts_enum_files_equal.
(* occurrence-keyed expression facts, built by the SINGLE bottom-up pass: visit_file refs have
   distinct NodeKeys, and the fact stored at a visited ref's key is EXACTLY that occurrence's fact (no
   overwrite; map-level exactness) — the single-pass fact map agrees with the per-node specification. *)
Print Assumptions Compilable.visit_file_key_nodup.
Print Assumptions Compilable.program_visit_key_nodup.
Print Assumptions Compilable.program_expr_facts_find.
Print Assumptions Compilable.program_expr_facts_eq_spec.
(* §3/§4/§5/§6 the retained-phase production path: the ONE [Compilable.Input] retains the visit as a STORED value
   that IS the snapshot's traversal ([Compilable.input_visit_ok]); the [Compilable.TypeNameFacts] is built from THAT retained visit
   ([Compilable.build_type_name_map]); the ONE proof-carrying [Compilable.WorkForest] OBJECT is built ONCE and RETAINS in its fields the
   exact pair-projection ([Compilable.forest_items_exact]), BOTH domains ([Compilable.forest_reverse] reverse / [Compilable.forest_forward] forward), the
   key-NoDup ([Compilable.forest_keys_nodup]), with a conversion's operand MEMBER in the PROCESSED suffix
   ([Compilable.forest_operand_in_tail]) — no [proj1_sig] discards its proof; the PROOF-CARRYING FOREST-INDEXED
   [Compilable.Outcomes] pairs the outcome map with its completeness proof so the query is TOTAL —
   [total_forest_outcome_at] CONSUMES a retained [WorkMember] and MATCHES the occurrence
   ([total_forest_outcome_at_matches]); the resolved-target query is the Index.table's stored fact
   ([type_name_fact_at_table_resolves]); and a stored conversion FAILURE's cause is read DIRECTLY off the
   retained forest Index.table, keyed by the WORK member — its refs are the work's own carried refs, the target type is
   the sealed Index.table's stored fact, the operand's outcome is read THROUGH the exact operand [SuffixMember]
   ([Compilable.accumulator_total acc_rest]) as a success whose status IS the reported one, and [Typing.convert_constant] genuinely rejects
   ([total_forest_outcome_cause] retaining the member/suffix-indexed [StepCause], inverted by
   [Compilable.conversion_failure_cause_yields_step]). *)
Print Assumptions Compilable.occurrences_file_operand.
Print Assumptions Compilable.input_visit_ok.
Print Assumptions Compilable.type_name_fact_at_table_resolves.
Print Assumptions Compilable.build_type_name_map.
Print Assumptions Compilable.forest_items_exact.
Print Assumptions Compilable.forest_reverse.
Print Assumptions Compilable.forest_forward.
Print Assumptions Compilable.forest_keys_nodup.
Print Assumptions Compilable.forest_operand_in_tail.
(* §3/§4/§10 THE EXACT STANDARD WORK-MEMBER INDEX — the retained ordered [Compilable.forest_items] list is the
   SOURCE-ORDER authority ONLY; the IDENTITY role is a DERIVED index whose storage and lookup delegate ENTIRELY to
   the pinned-stdlib [FMapAVL] map [Index.KeyMap].  NO keyed list scan — no [List.find], no [existsb]
   membership test, no recursive key search — occurs anywhere in the work-member lookup path
   ([build_outcome_trace] -> [build_conversion_step] -> [build_conversion_work] -> [forest_index_member_at] ->
   [index_member_at] -> [KeyMap.find]); the theory's one remaining [find] is [Names.classify], a
   spelling CLASSIFICATION over the fixed closed sixteen-name descriptor enumeration with a proved inverse, not
   stored keyed storage.  [Compilable.forest_keys_nodup] is a FACT about the ordered enumeration that LICENSES the index
   build — never the lookup mechanism.
   BUILD: [work_index_map] folds the ALREADY-BUILT item list once through the standard [add] (it takes the list,
   so it cannot re-traverse [Compilable.input_visit] or re-run [build_forest_blocks]); [work_index_fresh] / [work_index_add_fresh]
   prove every add writes a key the partial map does not yet hold, so the fold is OVERWRITE-FREE; [build_work_index]
   is TOTAL with no option/fallback/empty-default precisely because the key-NoDup is a PROOF ARGUMENT — a
   possibly-duplicated list cannot be handed to it.  [Compilable.forest_index] retains the index as a DEPENDENT field over the
   forest's own [Compilable.forest_items], so a foreign map is not pairable with a forest.
   EXACTNESS: [work_index_exact] / [Compilable.index_exact] pin [find] to "the retained item with this key" in BOTH directions
   (sound: every hit is a retained item at that key; complete: every retained item is found at its own key), so
   every item has exactly one entry and every entry is exactly one item.  [Compilable.index_domain] is the DERIVED domain
   (never a stored second authority); [Compilable.index_key_inj] derives from the standard map that two retained items with
   equal keys ARE the same item — so duplicate work keys are impossible and no equal-key FRESH [Compilable.Work] can
   substitute for a retained one ([Compilable.forest_key_inj] is now that theorem, not a hand-rolled NoDup list scan).
   QUERY: [index_member_at] / [forest_index_member_at] are the TOTAL member queries — ONE
   [KeyMap.find], the impossible [None] branch discharged by a Prop existence hypothesis (no Prop
   eliminated into the returned [sig], no fallback member).  [index_member_at_retained] /
   [forest_index_member_at_retained]: the query at a retained member's own key returns THAT member;
   [index_no_foreign] / [forest_index_no_foreign]: a key held by no retained item has no entry;
   [index_nonexpr_absent]: a VISITED non-expression occurrence has no entry (wrong-kind exclusion).
   CONVERSION PATH: [build_conversion_work] queries the index at the key of the operand [ExprRef] the work item
   ALREADY CARRIES ([Compilable.work_conv]) — never a separately guessed source value — and returns the [Compilable.Conversion] whose
   [Compilable.conversion_operand_work] is that exact member with its exact ref / key / role / source-expression proofs;
   [build_conversion_step] then places that SAME member in the processed suffix. *)
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
(* §3/§6 (REPAIR 9) the forest outcome Index.table IS THE INTRINSIC CAUSAL OBJECT: [build_forest_outcome_table] folds the
   [Compilable.Trace] whose cons node RETAINS the exact tail trace + tail accumulator + head member + [StepCause] over
   the EXACT tail ([build_outcome_trace]); the Index.table pairs [Compilable.outcomes_acc] with [Compilable.outcomes_trace] INDEXED by it (not freely
   pairable).  [total_forest_outcome_cause] PROJECTS the trace ([trace_retained_cause]) to each member's exact
   insertion [RetainedMemberCause] — the exact suffix split, the AUTHENTICATED tail [Compilable.Accumulator], the
   [StepCause] producing the FINAL outcome, and the tail-to-final QUERY PRESERVATION.  The direct cause is projected
   by inverting the [StepCause] (axiom-free) — [Compilable.conversion_success_cause_yields_step] returns the [ConversionStep] at the EXACT
   SOURCE [ts0]/[x0] supplied (the Compilable.ConversionSuccessCause constructor's own [Compilable.work_expr current = Syntax.Convert ts x] is injected against
   the premise, so no existential source-type distinction survives); [final_operand_outcome] specializes preservation
   to a conversion's operand, proving its FINAL-Index.table query EQUALS its retained tail query — the final-to-tail closure. *)
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
(* §3/§4/§5 the UNIVERSAL acceptance theorems over ANY retained Index.table/member: the direct
   conversion-success closure ([retained_convsuccess_closure] — the [ConversionStep] for the EXACT SOURCE [ts]/[x]
   (no existential ts0/x0) + target fact + operand SuffixMember + tail = final = Compilable.ExpressionSuccess opf + one Typing.convert_constant success
   + exact current fact), the direct child-failure closure +
   no-local-reason ([retained_childfail_closure] — operand fails in tail AND final, current Compilable.ChildFailure, current
   member emits no diagnostic), the stored-diagnostic connection ([retained_convfail_diag] — the exact
   Compilable.InvalidConversion over the STORED Compilable.ConversionFailure fields is a member of the projected list, read via
   [forest_awork_diags] not [local_conv_failure], returning the exact retained annotated member/context pair whose
   underlying work item IS that member), and UNIQUE trace insertion per work member
   ([outcome_trace_unique_step] — the trace's insertion sequence IS Compilable.forest_items, each once, key-NoDup). *)
Print Assumptions Compilable.retained_convsuccess_closure.
Print Assumptions Compilable.retained_childfail_closure.
Print Assumptions Compilable.retained_convfail_diag.
Print Assumptions Compilable.outcome_trace_unique_step.
Print Assumptions Compilable.trace_currents_eq.
(* §9.5 the SEPARATE spec bridge (NOT production-cause evidence): a member's [StepCause] AGREES with the index-free
   source specification [outcome_matches] given the operands' matches ([stepcause_matches], by construction in the
   fold); the total query at a retained member matches its own occurrence ([total_forest_outcome_at_matches]). *)
Print Assumptions Compilable.stepcause_matches.
Print Assumptions Compilable.total_forest_outcome_at_matches.
(* §7/§2.9 the forest outcome Index.table's domain is EXACTLY the RETAINED work forest's key set: every work item has an
   entry ([Compilable.outcomes_present]); the biconditional is over MEMBERSHIP in the retained enumeration [Compilable.forest_items]
   ([Compilable.outcomes_domain_iff_forest], NOT an [exists w] over any constructible [Compilable.Work]) — so a Index.table with the required
   entries plus any extra key is UNINHABITABLE; and a visited NON-expression occurrence has NO entry
   ([Compilable.outcomes_nonexpr_absent], wrong-kind exclusion). *)
Print Assumptions Compilable.outcomes_present.
Print Assumptions Compilable.outcomes_domain_iff_forest.
Print Assumptions Compilable.outcomes_nonexpr_absent.
(* §9 the TOTAL fact + diagnostic projections of the ONE forest outcome Index.table EQUAL the declarative specification
   (no fail-open: a missing outcome is never a case; the diagnostic emits the STORED refs).  §8/§2.3 the
   diagnostic is projected over the exact RETAINED annotated work ([forest_awork_diags], keyed by the work's own
   [Compilable.work_expr_ref] — NO [as_expr] with a fail-open [None] branch); [forest_awork_diags_eq] is its agreement with the
   source spec at the work's own occurrence. *)
Print Assumptions Compilable.forest_facts_eq_spec.
Print Assumptions Compilable.forest_awork_diags_eq.
Print Assumptions Compilable.expression_diagnostics_eq_spec.
Print Assumptions Compilable.expression_diags_eq_spec.
(* §7 THE ONE RETAINED ANNOTATED WORK OBJECT: [build_annotated_work_forest] constructs an
   [Compilable.AnnotatedWork] carrying (all field proofs axiom-free) the exact-members equality, the
   [annotate_program] fold-equivalence, and the four context-soundness properties; [Compilable.annotated_align_eq] is the
   occurrence/context alignment derived from the object's OWN carried fold (no rebuild); and
   [annotated_forest_erased_source] is the [aewf_spec_exact] surface — the erased annotation reproduces the
   EXPRESSION projection of the snapshot-independent [annotate_source]. *)
Print Assumptions Compilable.build_annotated_work_forest.
Print Assumptions Compilable.annotated_align_eq.
Print Assumptions Compilable.annotated_forest_erased_source.
(* package main-ref buckets built as ONE fold over the DELIVERED visit stream (no second
   per-file traversal): the whole-program buckets have the represented-package domain, each present bucket's
   length is the package's main count, on a valid program every bucket is a singleton (the one canonical
   main), and every main in a bucket belongs to that package. *)
Print Assumptions Compilable.program_package_refs_present.
Print Assumptions Compilable.program_package_refs_bucket_len.
Print Assumptions Compilable.program_package_refs_singleton_on_success.
Print Assumptions Compilable.program_package_refs_belongs.
(* the SEALED fact tables (no forged/foreign key possible): every key with an entry is a visited
   expression occurrence's key whose fact is exact; and on a valid program each package bucket is the one
   canonical main (the Compilable.Facts-level singleton projection). *)
Print Assumptions Compilable.program_expr_facts_domain.
Print Assumptions Compilable.package_singleton.
(* the expression-fact query is TOTAL on a valid Compilable.Facts: every typed ExprRef denotes a
   visited occurrence whose Typing.constant_info succeeds (so it has an exact entry), and the option-free query PROJECTS
   the sealed Index.table (returns exactly the stored fact — a defect-shipping option result is impossible). *)
Print Assumptions Compilable.expression_ref_fact_some.
Print Assumptions Compilable.expression_fact_at_find.
(* §8 the SEALED occurrence-keyed TYPE-NAME fact Index.table: the query is TOTAL (every TypeNameRef has a stored
   entry, needing no validity — a conversion's source name resolves by construction) and PROJECTS the sealed
   Index.table (returns exactly the stored fact); the stored fact EQUALS predeclared resolution of the SOURCE name
   recovered THROUGH the reference (no recompute, no spelling copy); and byte/uint8 (rune/int32) are DISTINCT
   source type syntax with EQUAL resolved-Typing.SemanticType facts. *)
Print Assumptions Compilable.type_name_ref_fact_some.
Print Assumptions Compilable.type_name_fact_at_find.
Print Assumptions Compilable.type_name_fact_at_resolves.
Print Assumptions Compilable.tnfact_byte_uint8_same_type.
Print Assumptions Compilable.tnfact_rune_int32_same_type.
Print Assumptions Compilable.tsyn_byte_neq_uint8.
Print Assumptions Compilable.tsyn_rune_neq_int32.
(* §5.2 the ONE closed conjunction pinning all SIXTEEN source-name mappings (14 numeric + byte->uint8 +
   rune->int32). *)
Print Assumptions Compilable.predeclared_all_sixteen.
(* §3.3 the conversion TARGET ref is obtained THROUGH the retained index (minted TypeNameRef): the exact
   Index.ConversionTarget child key, role Index.ConversionTarget, recovering the exact raw source Syntax.TypeExpr. *)
Print Assumptions Compilable.conversion_target_ref_conv.
(* §3.2/§10.2 the conversion OPERAND ref THROUGH the retained index: the exact Index.ConversionOperand child key,
   role Index.ConversionOperand, recovering the exact raw operand. *)
Print Assumptions Compilable.conversion_operand_ref_conv.
(* §8/§3.8 ONE EXPRESSION PHASE (OBJECT IDENTITY): the sealed FACTS and the DIAGNOSTICS are BOTH projections of
   the SAME retained [Compilable.phase_ot] outcome Index.table inside one [Compilable.Phase] ([facts_and_diags_share_phase]); and the
   type-name TABLE OBJECT sealed into a successful Compilable.Facts IS the [Compilable.phase_type_name_facts] of the phase actually built
   ([core_seals_tnfacts]) — quantified over the CONSTRUCTED object, not a global helper. *)
Print Assumptions Compilable.facts_and_diags_share_phase.
Print Assumptions Compilable.core_seals_tnfacts.
(* §8.1/§8.2/§9 THE DEPENDENT OBJECT CHAIN: the fact Index.table is a [Compilable.ExpressionFacts] indexed by the exact
   forest/outcome Index.table, carrying a proof its map IS the Compilable.ExpressionSuccess projection ([Compilable.expression_facts_is_facts]); the diagnostics are an
   [Compilable.Diagnostics] indexed by the exact retained [Compilable.AnnotatedWork] object and outcome Index.table,
   carrying a proof its list IS the projection ([Compilable.erased_is_diagnostics]).  A foreign equal-map Index.table / equal list is
   UNREPRESENTABLE — the dependent types encode the chain, not a provenance equality. *)
Print Assumptions Compilable.expression_facts_is_facts.
Print Assumptions Compilable.erased_is_diagnostics.
(* §11.2/§11.5 NO-RECONSTRUCTION SHARED OBJECT FLOW: each phase component IS the builder applied to the phase's OWN
   prior objects (definitional equality of the concrete [build_expression_phase] — one work-discovery let, passed
   forward; the sub-builders are forest/object-parameterized, so none re-runs [build_expr_work_forest]).  [Compilable.phase_ot]
   consumed [Compilable.phase_work]+[Compilable.phase_type_name_facts]; [Compilable.phase_awork] consumed [Compilable.phase_work]; [Compilable.phase_fact_table] consumed [Compilable.phase_work]+[Compilable.phase_ot]; [Compilable.phase_diag]
   consumed [Compilable.phase_awork]+[Compilable.phase_ot]. *)
Print Assumptions Compilable.phase_ot_consumes_work.
Print Assumptions Compilable.phase_awork_consumes_work.
Print Assumptions Compilable.phase_fact_table_consumes_work_outcomes.
Print Assumptions Compilable.phase_diag_consumes_awork_ot.
(* §9/§2.8 the fact-side seal by OBJECT IDENTITY: the Compilable.ExpressionFactTable OBJECT sealed into a successful
   Compilable.Facts IS [Compilable.expression_facts_table (Compilable.phase_fact_table)] of the phase actually built (not a fresh Index.table whose map merely
   equals the projection). *)
Print Assumptions Compilable.core_seals_facts.
(* §5/§2.9 the sealed type-name Index.table has RETAINED-INPUT PROVENANCE: it IS build_type_name_fact_table of the
   phase's own Compilable.Input — the phase's [Compilable.phase_type_name_facts] is DEFINITIONALLY that builder (no stored provenance
   equality; the concrete [build_expression_phase] let-binds it). *)
(* §5.3 repeated equal source names at DISTINCT occurrences -> DISTINCT target refs (distinct keys) with EQUAL
   recovered syntax and EQUAL sealed facts (occurrence identity, not name identity) — the universal (conditional)
   property AND its CONCRETE non-hypothetical instance on a real compiled two-[uint8] program (the two occurrences
   and their real minted TypeNameRefs DISCHARGED from the source, not assumed). *)
Print Assumptions Compilable.repeated_name_distinct_refs.
Print Assumptions Compilable.two_uint8_distinct_target_refs.
(* §15/§10.8 the deep-nested conversion phase fixtures: a valid four-deep nest compiles and its TOTAL
   diagnostic projection is EMPTY (no fail-open); a deep nest with an innermost overflow yields EXACTLY ONE
   diagnostic (no drop, no per-ancestor double-count). *)
Print Assumptions Compilable.deep_nested_compiles.
Print Assumptions Compilable.deep_nested_no_diags.
Print Assumptions Compilable.deep_fail_one_diag.
(* §12/§2.10 REAL PHASE fixtures: query [build_expression_phase]'s own [Compilable.phase_diags] projection — a deep valid chain
   projects EMPTY, a deep inner failure REPORTS (non-empty, not suppressed). *)
Print Assumptions Compilable.deep_nested_phase_no_diags.
Print Assumptions Compilable.deep_fail_phase_reports.
(* §12 DIRECT PRODUCTION-OBJECT phase queries (NOT spec rewrites): a REAL [Compilable.Work] of the deep program's
   retained input is built and [total_forest_outcome_at] is queried on the phase's OWN [Compilable.phase_ot] — the innermost
   int8(300) is the sole Compilable.ConversionFailure whose DIRECT cause reads the operand's stored Compilable.ExpressionSuccess (exact refs, no rescan);
   each enclosing conversion is Compilable.ChildFailure; the stored diagnostic list is EXACTLY ONE; the valid deep chain's
   conversions + leaf all resolve Compilable.ExpressionSuccess; the retained work forest has EXACTLY 5 items; and the production Index.table
   admits NO foreign key and NO wrong-kind (non-expression) key ([Compilable.phase_work]/[Compilable.phase_ot], not the specification). *)
(* §12/§6 the innermost convfail PROJECTS its RETAINED cause from the corrected outcome Index.table: the member's
   [total_forest_outcome_cause] destructs to the exact insertion [StepCause], inverted to the exact [ConversionStep]
   whose operand outcome — read THROUGH the exact operand [SuffixMember] via [Compilable.accumulator_total acc_rest] — is [Compilable.ExpressionSuccess opf],
   with ONE rejecting [Typing.convert_constant] and an [Compilable.ConversionFailure] naming that exact operand ref. *)
Print Assumptions Compilable.deep_fail_innermost_convfail.
Print Assumptions Compilable.deep_fail_outer_childfail.
Print Assumptions Compilable.deep_fail_exactly_one_diag.
Print Assumptions Compilable.deep_nested_all_ok.
Print Assumptions Compilable.over_program_failure_retains_rejected_core.
(* §10.1/§10.2/§10.3 — the production fixtures: the capability and the failure answered ONLY through
   themselves, and occurrence identity surviving into the retained accepted core. *)
Print Assumptions Compilable.deep_nested_capability_retains_elaboration.
Print Assumptions Compilable.deep_fail_capability_retains_rejected_elaboration.
Print Assumptions Compilable.twin_capability_retains_distinct_occurrences.
(* §10.1/§10.2 — the RETAINED CAUSAL HISTORY through the returned objects: the four conversion causes with
   their operand predecessors and convert_constant steps, the retained work index exact both ways, and on the
   rejected side the innermost failure, the enclosing child failures and the operand preservation.  These are
   the capability evidence; the generalised theorems they instantiate are stated over ANY retained phase. *)
Print Assumptions Compilable.deep_nested_capability_retains_causes.
Print Assumptions Compilable.deep_fail_capability_retains_rejected_causes.
Print Assumptions Compilable.forest_count_source.
Print Assumptions Compilable.member_at_in_forest.
Print Assumptions Compilable.core_prop_at_source.
(* §11.1/§11.4: the core retains the WHOLE elaboration — buckets, layout, plan and both
   diagnostic lists are stored with their exactness evidence, not recomputed on each query; and the
   rejected capability retains that exact core rather than a copied diagnostic list. *)
(* §1 RETAINED PACKAGE PROVENANCE: the built core's package map IS the fold of its OWN retained visit, and
   its raw diagnostics ARE that stored map's diagnostics — no step reruns [program_visit] or rebuilds the
   map.  The two canonical lemmas below are SPECIFICATION bridges only; no production query or capability
   fixture recovers a retained object through them. *)
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
(* §11.1 CORE CONSTRUCTION — exactly ONE of each, each STORED with the proof that it IS the canonical value.
   These are the retained record's own projections: gating them gates the retention itself, not a lemma about
   it.  One input and one phase need no exactness proof — [Phase] is INDEXED BY the input, so a phase built
   from a different input is not storable beside it. *)
Print Assumptions Compilable.core_input.
Print Assumptions Compilable.phase.
Print Assumptions Compilable.core_package_refs_from_visit.
Print Assumptions Compilable.core_layout_exact.
Print Assumptions Compilable.core_plan_exact.
Print Assumptions Compilable.core_raw_diagnostics_exact.
Print Assumptions Compilable.core_diagnostics_exact.
(* §11.2 DECISION — accepted IS the retained final diagnostic list being empty and rejected IS its being
   non-empty (the two are the capability's and the failure's own evidence fields, not a rerun of a checker);
   and each side matches whole-program admissibility exactly. *)
Print Assumptions Compilable.accepted.
Print Assumptions Compilable.rejected.
(* §11.3 SUCCESS — the ONE production mint path, and the two facts a witness needs about what it minted.
   Constructor opacity is NOT a Print-Assumptions surface: "this term does not typecheck" is not a theorem.
   It is enforced as the build fact it is, by the sealed-capability self-tests F-N in `make prove`. *)
Print Assumptions Compilable.capability_of_admissible.
Print Assumptions Compilable.capability_source.
Print Assumptions Compilable.capability_is_compile_outcome.
(* §11.4 FAILURE — the exposed diagnostics ARE the retained core's own, definitionally; the non-emptiness is
   the retained rejection evidence.  The failure carries the CORE; a diagnostic list carries nothing. *)
Print Assumptions Compilable.failure_nonempty.
Print Assumptions Compilable.deep_nested_seals_expression_fact_table.
Print Assumptions Compilable.phase_domain_exact.
(* §3/§4 the DIRECT FINAL-TO-TAIL CLOSURE + STORED-DIAGNOSTIC
   evidence, gated as the accepted public surfaces — each accepted theorem STATES exactly the evidence its proof
   obtains:
   - the exact per-occurrence valid-chain SUCCESS bundle ([deep_nested_convsuccess_at], proving [nested_success_bundle]:
     current Syntax.Convert view + current final Compilable.ExpressionSuccess f + the [ConversionStep] for the EXACT SOURCE [ts]/[x] of the bundle
     (no existential ts0/x0) + operand SuffixMember + tail = final = Compilable.ExpressionSuccess opf + tail=final query equality + ONE
     Typing.convert_constant success on the exact target fact + f the exact current Compilable.ExpressionFact), and its instantiation on ALL FOUR
     valid conversions ([deep_nested_chain_success_evidence]);
   - the innermost convfail's retained cause CONNECTED to the exact stored [Compilable.InvalidConversion]
     ([deep_fail_innermost_diag] — same fields, t = the exact predeclared-context target fact query
     [Compilable.fact_type (type_name_fact_at_table (Compilable.phase_type_name_facts phase) (Compilable.conversion_target_node_ref (Compilable.step_conversion step)))], the exact retained
     annotated member/context pair supplying [outer], and [Compilable.phase_diags] EXACTLY that singleton, no second reason);
   - the strong per-occurrence child-failure closure ([deep_fail_childfail_closure_at]: exact ConversionStep +
     operand + tail=final failure + current Compilable.ChildFailure + no local reason).
   The weaker projections are labeled COROLLARIES: [deep_nested_ok_closure_at] states only the operand tail/final
   Compilable.ExpressionSuccess + query equality (NO Typing.convert_constant success / target fact / current fact); the concrete aggregates
   [deep_fail_outer_operands_final_fail], [deep_nested_chain_operands_final_ok], [deep_nested_all_ok] state only the
   outcome SHAPE. *)
Print Assumptions Compilable.deep_nested_convsuccess_at.
Print Assumptions Compilable.deep_nested_chain_success_evidence.
Print Assumptions Compilable.deep_fail_innermost_diag.
Print Assumptions Compilable.deep_fail_childfail_closure_at.
Print Assumptions Compilable.deep_nested_ok_closure_at.
Print Assumptions Compilable.deep_fail_outer_operands_final_fail.
Print Assumptions Compilable.deep_nested_chain_operands_final_ok.
(* §3/§4/§10 the DIRECT WORK-INDEX fixtures over REAL programs:
   - [deep_nested_index_at] / [deep_nested_chain_index_evidence] — on the four-deep chain, EACH conversion's
     CARRIED operand [ExprRef] queries the retained standard-map index ([KeyMap.find]) to the EXACT
     retained operand member; that member IS the one the [ConversionStep] placed in the processed suffix
     ([Compilable.step_operand_exact] + [In … rest]); and the operand/current outcomes remain the accepted [Compilable.ExpressionSuccess] values;
   - [twin_expr_index_distinct] — the IDENTITY-DISTINCTION fixture: two occurrences carrying the LITERALLY SAME
     source expression value ([uint8(7)] twice) are DISTINCT work items with DISTINCT NodeKeys and DISTINCT index
     entries, each key answering with its OWN retained member.  Expression-value equality cannot conflate two
     retained members — the index keys OCCURRENCE identity.  (Its type-name-layer counterpart is
     [two_uint8_distinct_target_refs].) *)
Print Assumptions Compilable.deep_nested_index_at.
Print Assumptions Compilable.deep_nested_chain_index_evidence.
(* §4 the typed invalid-conversion reason DENOTES its code end-to-end (primary ExprRef, the exact minted target
   TypeNameRef, operand status, Typing.convert_constant rejects); the erased report RETAINS the source target spelling so
   invalid byte(...) vs uint8(...) (and rune vs int32) — same resolved Typing.SemanticType — erase DISTINGUISHABLY. *)
Print Assumptions Compilable.occurrence_expr_diags_conv_sound.
Print Assumptions Compilable.byte_uint8_erased_differ.
Print Assumptions Compilable.rune_int32_erased_differ.
(* the legacy compile class projects the elaboration diagnostics (matches the decision), not a rerun. *)
(* decision (expression half): every println argument resolves IFF program_typedb / Typing.Program. *)
Print Assumptions Compilable.expression_all_ok_program_typedb.
Print Assumptions Compilable.expression_all_ok_iff_typed_program.
(* EXPRESSION COMPLETENESS: no expression diagnostic IFF the program types (the diagnostics<->decision
   equivalence for the expression half). *)
Print Assumptions Compilable.emits_none_program_typedb.
Print Assumptions Compilable.expression_diags_empty_iff.
(* PACKAGE COMPLETENESS + the retained ELABORATION ROOT: no package diagnostic IFF every package satisfies
   the factored rules; no diagnostic at all IFF the elaboration decision holds; and elaboration succeeds/fails
   IFF Admissible/not. *)
Print Assumptions Compilable.sum_main_file.
(* the PRODUCTION (retained-bucket) package decision captures EACH factored rule EXACTLY: the redeclaration
   diagnostics are empty IFF [PackageDeclsUnique], the missing-entry diagnostics IFF [MainPackagesHaveEntry], and
   all package diagnostics together IFF [PackageRulesValid] — rooted DIRECTLY in the factored roots, NOT the
   exactly-one consequence. *)
Print Assumptions Compilable.redecl_diags_empty_iff_rules.
Print Assumptions Compilable.missing_diags_empty_iff_rules.
(* [Compilable.package_diags_empty_iff_rules] is the DIRECT factored-root surface; the older [Compilable.package_diags_empty_iff] (empty IFF
   the exactly-one CONSEQUENCE) it supersedes stays an internal lemma, covered by the whole-theory audit. *)
Print Assumptions Compilable.package_diags_empty_iff_rules.
Print Assumptions Compilable.semantic_diagnostics_empty_iff.
Print Assumptions Compilable.elaboration_accepted_iff_admissible.
Print Assumptions Compilable.elaboration_rejected_iff_inadmissible.

(* the LIVE source root is the FACTORED [SourceProgramValid] (= Typing.Program /\ PackageRulesValid,
   i.e. package-block uniqueness AND main-package entry as separate roots).  The retained universal theorem
   [current_package_rules_exactly_one] states the CURRENT-grammar consequence (the factored rules coincide with
   "every package has one main").  The DECIDABLE reflection is [source_spec_valid_b_iff] (and the decision-side
   [Compilable.semantic_ok_b_source_program_valid], gated above) — DIRECT, with no [prog_ok]/[ProgValid]. *)
Print Assumptions Compilable.current_package_rules_exactly_one.
(* the readable SPECIFICATION package reflection (for fixtures / proof convenience — NOT the production decision):
   [source_spec_package_rules_b] decides the two factored roots DIRECTLY (block uniqueness ↔ [PackageDeclsUnique],
   entry ↔ [MainPackagesHaveEntry]) — no combined "=1". *)
Print Assumptions Compilable.source_spec_package_rules_b_package_rules_valid.
Print Assumptions Compilable.source_spec_valid_b_iff.
(* Admissible INCLUDES the pinned one-shot `go build ./...` output PREFLIGHT.  The three
   diagnostic layers each have an emptiness/equivalence characterization (source, fresh, final); a failed
   preflight takes PRECEDENCE (exactly one build-output-directory diagnostic, hiding the sole package's semantic
   errors); Compilable.compile only PROJECTS the one elaboration (no second checker). *)
Print Assumptions Compilable.preflight_fails_iff.
Print Assumptions Compilable.semantic_diagnostics_empty_iff_source_valid.
Print Assumptions Compilable.fresh_build_diagnostics_nil_iff.
Print Assumptions Compilable.fresh_build_diagnostics_fail_singleton.
Print Assumptions Compilable.elaboration_diagnostics_nil_iff_admissible.
Print Assumptions Compilable.elaboration_diagnostics_eq_semantic.
Print Assumptions Compilable.elaboration_diagnostics_fresh_failure.
(* the FreshBuildPlan / final report / acceptance class depend on the ModuleSpec (the preflight's
   default exec name is a ModulePath.T function), so their determinism needs the FULL ProgramInputEqual, NOT
   FilesEqual alone (the counterexample: equal files, different module -> different plan). *)
Print Assumptions Compilable.root_layout_input_equal.
Print Assumptions Compilable.fresh_build_plan_input_equal.
Print Assumptions Compilable.erased_elaboration_report_input_equal.
(* the fresh BUILD PLAN and ROOT LAYOUT are RETAINED in Compilable.Facts (derived ONCE from
   the retained package buckets, whose keys ARE the selected package set), so a Compilable.Program PROJECTS the
   exact plan its elaboration used — never a recompute from the program. *)
Print Assumptions Compilable.bucket_keys_eq_selected.
Print Assumptions Compilable.fresh_build_plan_of_buckets.
Print Assumptions Compilable.program_build_plan_retained.
Print Assumptions Compilable.program_root_layout_retained.
(* the COMPLETE fresh-root-layout EXACTNESS: the "go.mod"->Compilable.GoModuleEntry entry (and it is the ONLY
   Compilable.GoModuleEntry key); a key maps to Compilable.SourceFileEntry IFF a root-level file has it; the DIRECTORY characterization
   (existing [root_layout_dir_iff]); and the whole no-extra-entry DOMAIN — plus the disjointness underpinning
   ([root_entry_hval] / [root_entry_key_neq_gomod]). *)
Print Assumptions Compilable.root_entry_key_neq_gomod.
Print Assumptions Compilable.root_entry_hval.
Print Assumptions Compilable.root_layout_dir_iff.
Print Assumptions Compilable.root_layout_gomod.
Print Assumptions Compilable.root_layout_gomod_iff.
Print Assumptions Compilable.root_layout_source_iff.
Print Assumptions Compilable.root_layout_domain.
(* the UNIVERSAL package-selection / import-path / executable-name / plan exactness (not just
   computed fixtures): visibility (a selected key IS a represented file's parent); the import-path INJECTIVITY
   in the package directory and its determinism (the directory key is recovered EXACTLY through the component
   authority) plus the nested string form; the NEVER-EMPTY default executable name, proved over the import
   path's COMPONENT LIST; the exact zero/single/multiple plan classification and the sole-main plan's stored
   output target. *)
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

(* Property: exact VALUE semantics — a zero literal and a negated zero agree; a resolved expression evaluates
   to a well-formed value of the resolved Typing.SemanticType (one type authority across compiler and runtime); value
   well-formedness reflection; an explicit INTEGER conversion carries its exact converted value (a float
   conversion rounds once); a string literal evaluates to the EXACT runtime byte sequence of its resolved
   type. *)
Print Assumptions Safe.eval_zero_sign_agnostic.
Print Assumptions Safe.eval_expr_resolved.
Print Assumptions Safe.eval_expr_resolved_type.
(* evaluation returns EXACTLY the resolved typed constant's stored value — a resolved float projects its
   packaged Float.runtime (no second round), stated generically and as the explicit float-runtime corollary. *)
Print Assumptions Safe.resolved_constant_value_float.
Print Assumptions Safe.eval_expr_resolved_value.
Print Assumptions Safe.eval_projects_stored_float_runtime.
Print Assumptions Safe.value_well_formedb_iff.
Print Assumptions Safe.typed_constant_to_value_denotes.
Print Assumptions Safe.eval_string_value.
Print Assumptions Safe.eval_string_resolved_type.
(* complex runtime: the typed-complex projection preserves type; a typed-complex runtime denotes its exact
   typed complex constant; a NaN / infinity / negative-zero component runtime value denotes NO constant;
   evaluation returns EXACTLY the stored Complex.typed_runtime. *)
Print Assumptions Safe.typed_constant_to_value_complex.
Print Assumptions Safe.value_denotes_complex_runtime.
Print Assumptions Safe.eval_projects_stored_complex_runtime.
Print Assumptions Safe.certify_retains_capability.
Print Assumptions Safe.certify_retains_core.

(* Render: all output ASCII (including conversions); the ONE Typing.ConstantInfo render-status root
   (Render.const_info_denotes: rendering denotes exactly the Typing.constant_info Typing computes) which is FUNCTIONAL
   (Render.const_info_denotes_functional: a rendered spelling denotes at most ONE Typing.ConstantInfo — the bool / bare
   integer / string / integer-conversion / bare float / float-conversion / complex-literal / complex-conversion
   recognisers are pairwise disjoint (and `complex(` is distinct from `complex64(`/`complex128(` at index 7), so
   no spelling admits two conflicting constant statuses) and the final
   resolved root (resolved argument -> const-status + well-formed value of its resolved type carrying the same
   constant); the integer-repair regressions (a bare integer above Integer.platform_maximum stays UNTYPED, does NOT denote a
   typed int, and only an explicit uint64 conversion assigns the type); the ten integer keywords are ASCII;
   the exact conversion spellings; decimal faithfulness + no leading zero; int boundaries; the header is the
   EXACT first line of a .go file; go.mod is rendered from the ModuleSpec — exact bytes, header first line,
   all ASCII. *)
Print Assumptions Render.file_ascii.
(* the import domain is INTRINSICALLY empty and the renderer STRUCTURALLY consumes [Syntax.imports], so a
   future import constructor forces a renderer update rather than being silently dropped. *)
Print Assumptions Render.source_imports_nil.
Print Assumptions Render.imports_nil_bytes.
Print Assumptions Render.expr_ascii.
Print Assumptions Render.const_info_denotes.
Print Assumptions Render.const_info_denotes_functional.
Print Assumptions Render.resolved_expr_denotes.
(* §11 the source type name is rendered from the RETAINED source identifier: distinct conversion type names
   render distinct text, so the byte/rune source aliases render "byte"/"rune" — distinct from "uint8"/"int32"
   even though they resolve to equal semantic types. *)
Print Assumptions Render.type_expr_inj.
Print Assumptions Render.conv_byte_neq_uint8.
Print Assumptions Render.conv_rune_neq_int32.
(* float rendering: the canonical decimal spelling + conversion spellings; ASCII; the decoder/renderer
   semantic round trip; a bare float denotes its exact rational, a conversion the rounded typed constant. *)
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
(* strings: the encoder/decoder round trip (an INDEPENDENT decoder inverts the canonical encoder); the
   rendered literal is all-ASCII even for bytes >= 128 and contains no raw newline/CR (quoting shape); every
   `\xhh` byte round-trips exactly (hex exactness); a boundary-byte escape spelling is pinned exactly *)
Print Assumptions Render.string_roundtrip.
Print Assumptions Render.string_literal_ascii.
Print Assumptions Render.string_literal_no_nl_cr.
Print Assumptions Render.hex_escape_exact.
Print Assumptions Render.string_denotes.
Print Assumptions Render.resolved_string_denotes.
(* complex rendering: the exact complex64/complex128 keywords are ASCII; the canonical complex(real, imag)
   literal renders exactly and is ASCII; the INDEPENDENT complex decoder round-trips the canonical spelling
  ; the conversion spellings; a bare complex literal denotes its exact Complex.Constant (the FUNCTIONAL
   denotation + final resolved root, gated generically above, now cover complex too). *)
Print Assumptions Render.complex_literal_ascii.
Print Assumptions Render.decode_render_complex_literal.
Print Assumptions Render.cplx_denotes.

(* Emit: the public emitter requires Safe.Program; the complete image is go.mod + the (possibly empty)
   .go map; the go.mod and every .go file begin with the header first line and are ASCII; on-disk .go
   paths are unique (duplicate paths impossible).  NO nonemptiness claim — the empty program is valid. *)
Print Assumptions Emit.of_safe_module_file_header.
Print Assumptions Emit.of_safe_module_file_ascii.
Print Assumptions Emit.of_safe_header.
Print Assumptions Emit.of_safe_ascii.
Print Assumptions Emit.image_keys_nodup.
(* rendering over the standard file map: the rendered map has the SAME key domain as the source; every
   binding is EXACTLY [Render.file] of its source; [FilesEqual] sources render to [FileMap.Equal] maps whose
   CANONICAL transport lists are EQUAL; and the whole [Emit.transport] is INDEPENDENT of input-node order. *)
Print Assumptions Emit.file_map_domain.
Print Assumptions Emit.file_map_binding.
Print Assumptions Emit.file_map_equal.
Print Assumptions Emit.entries_equal.
Print Assumptions Emit.transport_order_independent.
(* the Emit.Image BRIDGE: the rendered image REALIZES the fresh root layout the plan is
   computed over ([Emit.source_layout] over the image's own keys = [root_layout] over the source program), and
   its `.go` file keys are EXACTLY the source FilePaths (no extra entry; go.mod is a distinguished field). *)
Print Assumptions Emit.realizes_fresh_layout.
Print Assumptions Emit.files_are_source_paths.
(* the RETAINED-PLAN / IMAGE bridge: a rendered image realizes the Compilable.Program's RETAINED
   root layout ([Compilable.facts_root_layout]) AND the retained build plan's output-target classification is the ACTUAL
   image's classification at that output name — the collision check is against the real emitted tree. *)
Print Assumptions Emit.realizes_retained_layout.
Print Assumptions Emit.output_target_of_retained_plan.

(* Index (Source Forest): the PRODUCTION occurrence index over the ONE raw Syntax.Program grammar — Pillar 1
   (source/index exactness).  The sealed standard positive-key node-Index.table laws; the per-file occurrence-count
   equals the Index.table-free boundary function; and the load-bearing UNIVERSAL per-file source/index exactness
   theorem — the metadata the one-pass builder stores at every local id is EXACTLY the metadata of the exact
   source occurrence there (kind/role/parent/subtree, presence AND absence), against an INDEPENDENT Index.table-free,
   builder-independent source-occurrence specification over the real grammar (file root / package clause /
   declarations / statements / println arguments / conversion operands) — plus its consequences (A..H). *)
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
(* Index Pillar 2 — the structural navigation invariants over the built per-file index: the file index is
   well-formed; root id canonical / no parent, only the root has no parent, every non-root has a unique
   parent; the interval-jump direct-child enumeration is sound + complete (parent/child inverse) and source-
   ordered; the O(1) preorder-interval ancestor test is sound + complete; canonical enumeration is
   sound/complete/NoDup; the builder branches only on SHAPE (no structural-equality dedup); metadata stores no
   subtree copy. *)
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
(* Index Pillar 3 — the SEALED reference layer indexed by the exact Syntax.Program: decidable Index.Key identity;
   the sealed Snapshot API (index_program / file_of_path / ref_of_key / total ref_meta/kind/role/subtree/
   containing_file/parent_of/children_of/node_at/source_occurrence_of_ref/is_ancestor_ref) whose raw
   constructors are hidden; reference/file extensionality + Index.Key injectivity; total navigation (root has no
   parent / only root / parent same file / children same file / parent-child inverse both ways / source-ordered
   NoDup children / ref-level ancestry sound+complete); minting sound + complete + non-circular source
   membership; and the EXACT source-occurrence correspondence lifted through the sealed API (metadata / kind /
   role / parent / subtree / source view all pinned to the exact source occurrence). *)
Print Assumptions Index.key_eq_dec.
Print Assumptions Index.key_equalb_spec.
(* outer-index exactness: the derived outer index [outer_of] (which the sealed [Index.Syntax]'s internal
   map IS) holds, at every path, EXACTLY the per-file build of the program's file there and nothing at a path
   with no file — presence AND absence, so no entry can belong to another snapshot and none is spurious. *)
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
(* Index typed/kind-refined references: the kind-refiner is sound + complete + mismatch-rejecting, the
   refined kind is the EXACT source occurrence's kind (not a free boolean), and the erased Index.Key determines
   the typed-reference identity. *)
Print Assumptions Index.erase_as_kind.
Print Assumptions Index.as_kind_complete.
Print Assumptions Index.as_kind_mismatch.
Print Assumptions Index.noderefof_kind.
Print Assumptions Index.noderefof_key_inj.
(* Index ROOT-completeness surfaces: FileRef minting soundness + the invalid-path /
   invalid-local rejection cases; decidable NodeRef equality; and the CANONICAL preorder enumeration of ALL a
   file's references (same-file / complete / NoDup / source-ordered) with reachability of every occurrence from
   its file root by repeated parent links. *)
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
(* the canonical INDEXED TRAVERSAL: the structural one-pass occurrence fold is EXACT (lists exactly the
   graph of source_occurrence_at) and canonically ORDERED; lifted to the reference level, [visit_file] supplies
   each occurrence's validated NodeRef paired with its ORIGINAL syntax view TOGETHER — exact, same-file,
   complete over the file, in canonical source preorder order, NoDup (no per-node source recovery). *)
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
(* the retained Index.Program phase boundary: canonical construction reuses exactly the one
   Snapshot.index_program, and the retained index is the projected field. *)
Print Assumptions Index.index_program_syntax.
Print Assumptions Index.indexed_syntax_proj.
(* the canonical Index.Key ordered key + standard AVL map: ordered equality, add/find laws, and canonical
   elements as a function of the map's meaning (Equal maps enumerate identically). *)
Print Assumptions Index.key_compare_equal.
Print Assumptions Index.key_map_add_equal.
Print Assumptions Index.key_map_add_unequal.
Print Assumptions Index.key_map_elements_equal.
(* the UNIVERSAL query-projection bridge: every typed expression query PROJECTS its occurrence's
   EXACT analyzed fact (the const-status the fact Index.table stores).  (The concrete per-program erased-report /
   fact-enumeration / single-failure-scar fixtures stay COMPILED as tests + covered by the whole-theory audit,
   but are NOT gated surfaces — they are fixed-program witnesses, not universal claims.) *)
Print Assumptions Compilable.expression_fact_at_exact.
(* the UNIVERSAL STRICT canonical-order theorem: the report's node-primary diagnostics appear in
   STRICTLY ascending Index.Key order (path then local id) via the standard Index.KeyMap's key-sorted elements —
   NO project-authored sort.  Backed by the two supporting claims the order rests on: the node-keyed INPUT has
   UNIQUE keys (expr keys NoDup + pkg keys NoDup + their disjointness), so every bucket is a SINGLETON — hence
   there are NO within-bucket ties to reorder; the bucketing is a REORDERING and the report has exactly the
   diagnostics of `Compilable.expression_diags ++ Compilable.package_diags`. *)
Print Assumptions Compilable.collect_node_input_nodup.
Print Assumptions Compilable.collect_node_buckets_singleton.
Print Assumptions Compilable.semantic_diagnostics_node_strict.
Print Assumptions Compilable.collect_diagnostics_in.
(* the SOURCE characterization of the erased report (ties the report to its source form; the universal
   diagnostic-exactness claims above rest on it). *)
Print Assumptions Compilable.erased_report_src_eq.
