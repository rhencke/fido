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
   exact 64-bit int/uint; generic min/max accepted and below-min/above-max rejected; keyword exactness +
   injectivity; int<>int64 and uint<>uint64 distinct despite equal ranges; the derived default-int bounds. *)
Print Assumptions Ints.integer_type_eqb_eq.
Print Assumptions Ints.integer_representableb_spec.
Print Assumptions Ints.IInt_bits_64.
Print Assumptions Ints.IUint_bits_64.
Print Assumptions Ints.integer_min_representable.
Print Assumptions Ints.integer_max_representable.
Print Assumptions Ints.integer_min_pred_not_representable.
Print Assumptions Ints.integer_max_succ_not_representable.
Print Assumptions Ints.integer_keyword_exact.
Print Assumptions Ints.integer_keyword_inj.
Print Assumptions Ints.IInt_neq_IInt64.
Print Assumptions Ints.IUint_neq_IUint64.
Print Assumptions Ints.int_min_val.
Print Assumptions Ints.int_max_val.
Print Assumptions Ints.uint_max_val.

(* the ONE float-family authority (Floats.v, axiom-free over SpecFloat): FloatType equality; exact keywords;
   precision/exponent settings; direct binary32/binary64 rounding of exact rationals; the double-rounding
   counterexample (direct F32 differs from binary64-then-binary32); precision boundaries 2^24+1 / 2^53+1. *)
Print Assumptions Floats.float_type_eqb_eq.
Print Assumptions Floats.float_keyword_F32.
Print Assumptions Floats.float_keyword_F64.
Print Assumptions Floats.float_prec_F32.
Print Assumptions Floats.float_prec_F64.
Print Assumptions Floats.float_emax_F32.
Print Assumptions Floats.float_emax_F64.
Print Assumptions Floats.scar_direct_f32.
Print Assumptions Floats.scar_double_f32_via_f64.
Print Assumptions Floats.scar_direct_differs_double.
Print Assumptions Floats.round_f32_2p24_plus1.
Print Assumptions Floats.round_f64_2p53_plus1.
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
Print Assumptions Floats.round_const_scar_direct_f32.
Print Assumptions Floats.round_const_overflow_f32.
Print Assumptions Floats.round_const_underflow_f64.
Print Assumptions Floats.round_const_source_zero_f64.
(* the intrinsic finite-decimal raw literal domain: equality by canonical representation (proof-irrelevant
   well-formedness); the exact rational value is canonical; the unique (0,0) zero -> unsigned zero; a bound /
   non-canonical fixture rejects. *)
Print Assumptions Floats.dm_eqb_eq.
Print Assumptions Floats.decimal_value_canonical.
Print Assumptions Floats.decimal_value_zero.
Print Assumptions Floats.decimal_zero_unique.
Print Assumptions Floats.decimal_wfb_max_ok.
Print Assumptions Floats.decimal_wfb_coeff_over.
Print Assumptions Floats.decimal_value_1p5.
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
Print Assumptions Floats.round_typed_neg_underflow_f64.
Print Assumptions GoTypes.convert_const_same_float.
Print Assumptions GoTypes.typed_const_exact.
Print Assumptions GoSafe.typed_const_to_value_type.
Print Assumptions GoSafe.typed_const_to_value_wf.
Print Assumptions GoSafe.typed_const_to_value_float.
Print Assumptions GoSafe.eval_expr_denotes.
Print Assumptions GoSafe.value_denotes_constant_runtime.
Print Assumptions GoSafe.float_nonconstant_no_denotes.
Print Assumptions GoSafe.nan_f64_no_denotes.
Print Assumptions GoSafe.inf_f64_no_denotes.
Print Assumptions GoSafe.neg_zero_f64_no_denotes.

(* Complexes — the ONE complex-type authority, COMPOSED from the Floats component authority: decidable
   ComplexType equality; the exact keywords; the ONE component mapping (C64->F32, C128->F64) sourcing all
   precision; exact ComplexConst equality; the decimal-complex exact value projections; round_typed_complex's
   componentwise results (each rounds ONCE) + representability reflection + component-overflow rejection;
   underflow-to-+0 + no-NaN/Inf/-0 runtime component shape (inherited from TypedFloatConst); the runtime
   component read-back coherence. *)
Print Assumptions Complexes.complex_type_eqb_eq.
Print Assumptions Complexes.complex_keyword_C64.
Print Assumptions Complexes.complex_keyword_C128.
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
Print Assumptions FilePath.ok_main.
Print Assumptions FilePath.no_dotdot.
Print Assumptions FilePath.no_test.
Print Assumptions FilePath.no_testdata.
Print Assumptions FilePath.no_vendor.

(* intrinsic ModulePath: decidable equality; a representable canonical module path; rejected
   (unrepresentable) module paths.  Invalid module paths have no ModulePath value at all. *)
Print Assumptions ModulePath.mp_eqb_eq.
Print Assumptions ModulePath.ok_generated.
Print Assumptions ModulePath.no_dotdot.
Print Assumptions ModulePath.no_leading_slash.
Print Assumptions ModulePath.no_at.
Print Assumptions ModulePath.no_reserved_con.
Print Assumptions ModulePath.no_dotless_go.
Print Assumptions ModulePath.no_ver_v1.
Print Assumptions ModulePath.no_gopkg_bare.

(* intrinsic GoVersion: the singleton Go1_23 renders EXACTLY "1.23"; decidable equality *)
Print Assumptions GoVersion.render_goversion_go1_23.
Print Assumptions GoVersion.goversion_eqb_eq.

(* the ONE standard-collection foundation (C1A): the [FilePath] ordered key and the standard AVL/positive
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
Print Assumptions GoTypes.float_default_resolved.
Print Assumptions GoTypes.str_representable.
Print Assumptions GoTypes.const_representableb_iff.
Print Assumptions GoTypes.const_scar_direct.
Print Assumptions GoTypes.const_int8_int16_127.
Print Assumptions GoTypes.resolve_expr_sound.
Print Assumptions GoTypes.resolve_expr_complete.
Print Assumptions GoTypes.resolve_expr_deterministic.
Print Assumptions GoTypes.stmt_typedb_iff.
Print Assumptions GoTypes.program_typedb_iff.
Print Assumptions GoTypes.empty_program_typed.
(* §7 map-based typing is ORDER-INDEPENDENT: it respects semantic map equality (as a Prop and reflected as a
   bool) and is therefore invariant under reordered [build_program] construction. *)
Print Assumptions GoTypes.ProgramTyped_Equal.
Print Assumptions GoTypes.program_typedb_Equal.
Print Assumptions GoTypes.program_typedb_build_permutation.
(* §20 — the per-occurrence typing predicate folded over the canonical source occurrence stream equals the
   existing [source_file_typedb] (the leaf GoCompile's analysis consumes; the C2 indexed whole-program checker
   is removed, §19/§26). *)
Print Assumptions GoTypes.occs_file_typedb_eq.
(* C3 §6 — the one-node semantic step: [const_info] reflects [const_info_step] applied to its child's status
   (the reusable one-pass leaf authority; convert_const stays the sole conversion authority). *)
Print Assumptions GoTypes.const_info_step_reflect.
(* type-at-use: a bare literal defaults to int; the int boundaries resolve, one past does not; a huge
   (>2^64) constant is exact but resolves to no integer type; explicit uint64/int64 type-at-use behaviour *)
Print Assumptions GoTypes.res_int_default.
Print Assumptions GoTypes.res_int_max.
Print Assumptions GoTypes.res_int_min.
Print Assumptions GoTypes.res_over.
Print Assumptions GoTypes.res_under.
Print Assumptions GoTypes.res_huge_no_resolve.
Print Assumptions GoTypes.res_uint64_2p63.
Print Assumptions GoTypes.res_int64_2p63_reject.
(* per-type conversion boundaries (int8/uint8/uint64 min/max +/-1) and transitive nested-conversion cases *)
Print Assumptions GoTypes.res_int8_min.
Print Assumptions GoTypes.res_int8_max.
Print Assumptions GoTypes.res_int8_under.
Print Assumptions GoTypes.res_int8_over.
Print Assumptions GoTypes.res_uint8_0.
Print Assumptions GoTypes.res_uint8_255.
Print Assumptions GoTypes.res_uint8_m1.
Print Assumptions GoTypes.res_uint8_256.
Print Assumptions GoTypes.res_uint64_max.
Print Assumptions GoTypes.res_uint64_over.
Print Assumptions GoTypes.const_int8_int16_127.
Print Assumptions GoTypes.const_int8_int16_128_reject.
Print Assumptions GoTypes.const_uint8_int_300_reject.
Print Assumptions GoTypes.conv_bool_reject.
Print Assumptions GoTypes.conv_str_reject.
(* type identity: int<>int64 and uint<>uint64 as distinct STATIC types *)
Print Assumptions GoTypes.tint_neq_tint64.
Print Assumptions GoTypes.tuint_neq_tuint64.
(* cross-kind non-resolution: a bool does not resolve as an integer, an integer not as bool, a string not as
   an integer; no string const is representable as an integer; an arbitrary-byte string resolves as TString;
   a mixed bool/int/string println statement is typed *)
Print Assumptions GoTypes.bool_not_resolve_int.
Print Assumptions GoTypes.int_not_resolve_bool.
Print Assumptions GoTypes.str_not_resolve_int.
Print Assumptions GoTypes.cstr_not_int.
Print Assumptions GoTypes.res_str_bytes.
Print Assumptions GoTypes.str_representable.
Print Assumptions GoTypes.str_representableb.
Print Assumptions GoTypes.stmt_mixed_str_typed.
(* floats: a bare float defaults to float64; explicit F32/F64 conversions type at use; float->integer
   constant conversions (integral+in-range accept, fraction/overflow reject); wrong-type reject; TFloat F32
   and F64 are distinct; ★the direct-vs-nested double-round scar analyzes to DIFFERENT typed constants;
   a default-overflowing bare float does not type. *)
Print Assumptions GoTypes.res_float_default.
Print Assumptions GoTypes.res_float32_conv.
Print Assumptions GoTypes.res_float64_conv.
Print Assumptions GoTypes.res_int_of_3_0.
Print Assumptions GoTypes.res_int_of_3_5_rej.
Print Assumptions GoTypes.res_int8_128_0_rej.
Print Assumptions GoTypes.res_uint8_m1_0_rej.
Print Assumptions GoTypes.res_float32_true_rej.
Print Assumptions GoTypes.res_float64_str_rej.
Print Assumptions GoTypes.tfloat32_neq_tfloat64.
Print Assumptions GoTypes.const_scar_direct.
Print Assumptions GoTypes.const_scar_nested.
Print Assumptions GoTypes.const_scar_direct_differs_nested.
Print Assumptions GoTypes.stmt_float_mixed.
Print Assumptions GoTypes.stmt_float_overflow_untyped.
(* complex: TCComplex exact-value erasure (§14 UNIVERSAL same-type complex identity convert_const_same_complex);
   bare complex DEFAULTS to complex128; explicit complex64/complex128 resolve; C64<>C128 distinct; a matching-
   format typed float REUSES the real component; a matching-format typed complex PROJECTS to the scalar;
   integer/float -> complex; zero-imaginary complex -> integer/float; nonzero-imaginary / component-overflow /
   wrong-type reject; ★the direct-vs-nested COMPONENT double-round scar analyzes to DIFFERENT typed constants. *)
Print Assumptions GoTypes.convert_const_same_complex.
Print Assumptions GoTypes.convert_complex_reuses_float_component.
Print Assumptions GoTypes.convert_float_reuses_complex_component.
Print Assumptions GoTypes.type_untyped_int_convert.
Print Assumptions GoTypes.type_untyped_float_convert.
Print Assumptions GoTypes.type_untyped_complex_convert.
Print Assumptions GoTypes.res_cplx_default.
Print Assumptions GoTypes.res_cplx64.
Print Assumptions GoTypes.res_cplx128.
Print Assumptions GoTypes.cplx_types_distinct.
Print Assumptions GoTypes.cplx64_from_f32_real.
Print Assumptions GoTypes.f32_of_cplx64_real.
Print Assumptions GoTypes.res_cplx64_int.
Print Assumptions GoTypes.res_cplx64_float.
Print Assumptions GoTypes.res_int_of_cplx3.
Print Assumptions GoTypes.res_f32_of_cplx1p5.
Print Assumptions GoTypes.res_int_of_cplx_nonzero_imag_rej.
Print Assumptions GoTypes.res_f32_of_cplx_nonzero_imag_rej.
Print Assumptions GoTypes.res_cplx64_real_over.
Print Assumptions GoTypes.res_cplx64_bool_rej.
Print Assumptions GoTypes.res_int_of_cplx3p5_rej.
Print Assumptions GoTypes.conv_c64_c64.
Print Assumptions GoTypes.cplx_real_3_2.
Print Assumptions GoTypes.cplx_imag_m5_2.
Print Assumptions GoTypes.cplx_scar_direct_vs_nested.
Print Assumptions GoTypes.cplx_scar_direct_real.
Print Assumptions GoTypes.cplx_scar_nested_real.
Print Assumptions GoTypes.cplx_scar_imag_direct_vs_nested.
Print Assumptions GoTypes.cplx_underflow_pos_zero.
Print Assumptions GoTypes.cplx_tiny_imag_untyped_nonzero.
Print Assumptions GoTypes.int_of_cplx_tiny_imag_rej.
Print Assumptions GoTypes.cplx64_tiny_imag_rounds_zero.
Print Assumptions GoTypes.int_of_cplx64_tiny_imag_ok.
Print Assumptions GoTypes.int_of_cplx64_tiny_imag_is_3.

(* C1A: the map-backed SOURCE FOREST — [GoProgram]'s files are a STANDARD FilePath map ([GoFileMap]).  The
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

(* GoCompile (A) internal exactness: whole-program prog_ok reflects the declarative judgment; go_compile
   sound + complete against it; a rejected program yields no CompilableProgram; the compiled evidence exposes
   that the same program is typed; the empty program is accepted; a concrete integer-family program compiles;
   an out-of-range and an invalid-nested-conversion program are rejected with the honest typing error (and
   have no CompilableProgram); a concrete string program compiles. *)
Print Assumptions GoCompile.prog_ok_iff.
Print Assumptions GoCompile.go_compile_ok_valid.
Print Assumptions GoCompile.go_compile_complete.
(* C3 §18/§21 — PROVENANCE + RETENTION: every CompilableProgram's facts ARE analyze's exact AnalysisOK output
   (no parallel capability path), and it RETAINS the exact analyzed index (the projection retains, never
   reconstructs). *)
Print Assumptions GoCompile.compilable_prov.
Print Assumptions GoCompile.compilable_index_retained.
(* §8 map-based PACKAGE GROUPING via a standard [PackageMap] in ONE [FM.fold]: EXACTNESS (every file
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
Print Assumptions GoCompile.GoCompile_Equal.
Print Assumptions GoCompile.prog_ok_Equal.
Print Assumptions GoCompile.go_compile_class_Equal.
Print Assumptions GoCompile.go_compile_class_build_permutation.
Print Assumptions GoCompile.reject_no_compile.
Print Assumptions GoCompile.compilable_program_typed.
Print Assumptions GoCompile.prog_ok_empty.
Print Assumptions GoCompile.int_program_ok.
Print Assumptions GoCompile.int_program_compiles.
Print Assumptions GoCompile.over_program_rejected.
Print Assumptions GoCompile.bad_convert_rejected.
Print Assumptions GoCompile.bad_convert_no_compile.
Print Assumptions GoCompile.str_program_ok.
Print Assumptions GoCompile.str_program_compiles.
Print Assumptions GoCompile.float_program_compiles.
Print Assumptions GoCompile.float_reject_rejected.
Print Assumptions GoCompile.float_reject_no_compile.
(* §50 a whole COMPLEX program (bare default + complex64/complex128 conversions + scalar->complex +
   zero-imaginary complex->scalar) is typed and compiles; a component-overflow and a nonzero-imaginary
   complex->int program are honest typing rejections with no CompilableProgram. *)
Print Assumptions GoCompile.complex_program_typed.
Print Assumptions GoCompile.complex_program_compiles.
Print Assumptions GoCompile.complex_overflow_rejected.
Print Assumptions GoCompile.complex_overflow_no_compile.
Print Assumptions GoCompile.complex_nonzero_imag_no_compile.
(* C3 §7 — PackageRef: a validated package-key absence anchor.  Key identity determines the ref (UIP over the
   boolean membership proof), the key names a represented package, and construction from a binding / file
   reference yields the right key. *)
Print Assumptions GoCompile.package_ref_present.
Print Assumptions GoCompile.package_ref_key_inj.
Print Assumptions GoCompile.package_ref_of_binding_key.
Print Assumptions GoCompile.package_ref_of_fileref_key.
(* C3 §8 — structured diagnostic core: the primary anchor is an exact-snapshot handle whose kind matches the
   reason's code (invalid anchor/category combinations are unrepresentable). *)
Print Assumptions GoCompile.diagnostic_code_primary_consistent.
(* C3 §9 — END-TO-END diagnostic soundness (each diagnostic DENOTES its reported code): an invalid-conversion
   diagnostic's primary is the occurrence's OWN ExprRef, its syntax IS the explicit conversion to the reported
   target of some operand x, the reported operand status is x's exact ConstInfo, and [convert_const] genuinely
   REJECTS it; a default-not-representable diagnostic is a genuine println argument whose exact untyped constant
   does NOT default and whose target is exactly the Go default; a missing-main is an EMPTY bucket at a
   represented package key; a duplicate-main relates a strictly-later main to the first canonical main — both
   genuine top-level (func main) declarations in the SAME package. *)
Print Assumptions GoCompile.occ_expr_diags_conv_sound.
Print Assumptions GoCompile.occ_expr_diags_default_sound.
Print Assumptions GoCompile.pkg_diag_of_bucket_missing_sound.
Print Assumptions GoCompile.pkg_diag_of_bucket_dup_sound.
Print Assumptions GoCompile.pkg_diags_dup_sound.
(* C3 §16/§17 — cross-snapshot determinism FOUNDATION: the KEYED visit stream (each visited reference's NodeKey
   + its source occurrence) depends ONLY on the file map, so FilesEqual programs have IDENTICAL keyed streams
   (the basis for equal erased reports / fact enumerations). *)
Print Assumptions GoCompile.keyed_visit_FilesEqual.
(* C3 §17 — THE cross-snapshot determinism theorem: two programs with the SAME file map (whose diagnostics
   live in DIFFERENT dependent snapshot types) produce the IDENTICAL erased report — it depends ONLY on the
   file map, never on the snapshot index or the backing AVL shape.  The expression half factors through
   [annotate_source] (the one-pass enclosing context erases to a source function of the keyed stream); the
   package half through the keyed source buckets ([ppkg_erased_find] + PackageMap canonical elements). *)
Print Assumptions GoCompile.annotate_encl_erased.
Print Assumptions GoCompile.ppkg_erased_find.
Print Assumptions GoCompile.erased_expr_diags_source.
Print Assumptions GoCompile.erased_pkg_diags_FilesEqual.
Print Assumptions GoCompile.erased_report_FilesEqual.
(* C3 §17 — construction-permutation corollary: building the same module from a PERMUTED file-node list
   yields the IDENTICAL erased report (the report is invariant to the proposer's file order). *)
Print Assumptions GoCompile.erased_report_build_permutation.
(* C3 §10/§14 — occurrence-keyed expression facts, built by the SINGLE bottom-up pass: visit_file refs have
   distinct NodeKeys, and the fact stored at a visited ref's key is EXACTLY that occurrence's fact (no
   overwrite; map-level exactness) — the single-pass fact map agrees with the per-node specification. *)
Print Assumptions GoCompile.visit_file_key_nodup.
Print Assumptions GoCompile.prog_visit_key_nodup.
Print Assumptions GoCompile.prog_expr_facts_find.
Print Assumptions GoCompile.prog_expr_facts_eq_spec.
(* C3 §14 — the occurrence-keyed status map is ONE fold over the DELIVERED visit stream ([prog_status_map],
   reading each conversion's operand at [operand_key] from the already-folded tail via [psm_fold_find] +
   [prog_visit_operand_closed]): its find at a visited occurrence's key is EXACTLY that occurrence's exact
   const_info (and each conversion operand's) — one const_info_step per occurrence, no separate source
   recursion, read O(1). *)
Print Assumptions GoCompile.occs_file_operand.
Print Assumptions GoCompile.prog_status_map_find.
Print Assumptions GoCompile.prog_status_map_find_operand.
Print Assumptions GoCompile.expr_diags_eq_spec.
(* C3 §14/§28 — package main-ref buckets built as ONE fold over the DELIVERED visit stream (no second
   per-file traversal): the whole-program buckets have the represented-package domain, each present bucket's
   length is the package's main count, on a valid program every bucket is a singleton (the one canonical
   main), and every main in a bucket belongs to that package. *)
Print Assumptions GoCompile.prog_package_refs_present.
Print Assumptions GoCompile.prog_package_refs_bucket_len.
Print Assumptions GoCompile.prog_package_refs_singleton_on_success.
Print Assumptions GoCompile.prog_package_refs_belongs.
(* C3 §10/§12 — the SEALED fact tables (no forged/foreign key possible): every key with an entry is a visited
   expression occurrence's key whose fact is exact; and on a valid program each package bucket is the one
   canonical main (the CompilationFacts-level singleton projection). *)
Print Assumptions GoCompile.prog_expr_facts_domain.
Print Assumptions GoCompile.cf_package_singleton.
(* C3 §10/§27 — the expression-fact query is TOTAL on a valid CompilationFacts: every typed ExprRef denotes a
   visited occurrence whose const_info succeeds (so it has an exact entry), and the option-free query PROJECTS
   the sealed table (returns exactly the stored fact — a defect-shipping option result is impossible). *)
Print Assumptions GoCompile.expr_ref_fact_some.
Print Assumptions GoCompile.expr_fact_at_find.
(* C3 §18 — the legacy compile class projects the analysis diagnostics (matches the decision), not a rerun. *)
Print Assumptions GoCompile.go_compile_class_spec.
(* C3 decision (expression half): every println argument resolves IFF program_typedb / ProgramTyped. *)
Print Assumptions GoCompile.expr_all_ok_program_typedb.
Print Assumptions GoCompile.expr_all_ok_ProgramTyped.
(* C3 EXPRESSION COMPLETENESS: no expression diagnostic IFF the program types (the diagnostics<->decision
   equivalence for the expression half). *)
Print Assumptions GoCompile.emits_none_program_typedb.
Print Assumptions GoCompile.expr_diags_empty_iff.
(* C3 PACKAGE COMPLETENESS + the retained ANALYSIS ROOT: no package diagnostic IFF every package has one main;
   no diagnostic at all IFF the analysis decision holds; and analysis succeeds/fails IFF ProgValid/not. *)
Print Assumptions GoCompile.sum_main_file.
Print Assumptions GoCompile.pkg_diags_empty_iff.
Print Assumptions GoCompile.collect_diagnostics_empty_iff.
Print Assumptions GoCompile.analyze_ok_iff_ProgValid.
Print Assumptions GoCompile.analyze_failed_iff_not_ProgValid.
(* C3 decision (package half + combined): every package has one main IFF AllPackagesOneMain; the combined
   analysis decision equals ProgValid (= GoCompile) — the AnalysisOK<->GoCompile decision core. *)
Print Assumptions GoCompile.pkg_all_ok_AllPackagesOneMain.
Print Assumptions GoCompile.analysis_ok_b_ProgValid.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree; a resolved expression evaluates
   to a well-formed value of the resolved GoType (one type authority across compiler and runtime); value
   well-formedness reflection; an explicit INTEGER conversion carries its exact converted value (a float
   conversion rounds once); a string literal evaluates to the EXACT runtime byte sequence of its resolved
   type. *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.
Print Assumptions GoSafe.eval_expr_resolved.
Print Assumptions GoSafe.eval_expr_resolved_type.
(* §29.5 evaluation returns EXACTLY the resolved typed constant's stored value — a resolved float projects its
   packaged tfc_runtime (no second round), stated generically and as the explicit float-runtime corollary. *)
Print Assumptions GoSafe.resolved_const_value_float.
Print Assumptions GoSafe.eval_expr_resolved_value.
Print Assumptions GoSafe.eval_projects_stored_float_runtime.
Print Assumptions GoSafe.value_wfb_iff.
Print Assumptions GoSafe.typed_const_to_value_denotes.
Print Assumptions GoSafe.eval_string_value.
Print Assumptions GoSafe.eval_string_resolved_type.
(* float runtime values: a bare float evaluates to a float64 value; an exact float->int constant to that
   integer; ★the direct-vs-nested scar as an EXACT uint64 integer observation; constant underflow -> +0. *)
Print Assumptions GoSafe.eval_float_type.
Print Assumptions GoSafe.eval_int_of_3_0.
Print Assumptions GoSafe.eval_scar_direct.
Print Assumptions GoSafe.eval_scar_nested.
Print Assumptions GoSafe.eval_scar_differ.
Print Assumptions GoSafe.eval_underflow_pos_zero.
Print Assumptions GoSafe.eval_neg_underflow_pos_zero.
(* complex runtime: the typed-complex projection preserves type; a typed-complex runtime denotes its exact
   typed complex constant; a NaN / infinity / negative-zero component runtime value denotes NO constant;
   evaluation returns EXACTLY the stored typed_complex_runtime (§34). *)
Print Assumptions GoSafe.typed_const_to_value_complex.
Print Assumptions GoSafe.value_denotes_complex_runtime.
Print Assumptions GoSafe.complex_nan_real_no_denotes.
Print Assumptions GoSafe.complex_inf_imag_no_denotes.
Print Assumptions GoSafe.complex_neg_zero_no_denotes.
Print Assumptions GoSafe.eval_projects_stored_complex_runtime.
Print Assumptions GoSafe.eval_cplx_scar_direct.
Print Assumptions GoSafe.eval_cplx_scar_nested.
Print Assumptions GoSafe.eval_cplx_scar_differ.

(* GoRender: all output ASCII (including conversions); the ONE ConstInfo render-status root
   (render_const_info_denotes: rendering denotes exactly the const_info GoTypes computes) which is FUNCTIONAL
   (render_const_info_denotes_functional: a rendered spelling denotes at most ONE ConstInfo — the bool / bare
   integer / string / integer-conversion / bare float / float-conversion / complex-literal / complex-conversion
   recognisers are pairwise disjoint (and `complex(` is distinct from `complex64(`/`complex128(` at index 7), so
   no spelling admits two conflicting constant statuses) and the final
   resolved root (resolved argument -> const-status + well-formed value of its resolved type carrying the same
   constant); the §4 integer-repair regressions (a bare integer above int_max stays UNTYPED, does NOT denote a
   typed int, and only an explicit uint64 conversion assigns the type); the ten integer keywords are ASCII;
   the exact conversion spellings; decimal faithfulness + no leading zero; int boundaries; the header is the
   EXACT first line of a .go file; go.mod is rendered from the ModuleSpec — exact bytes, header first line,
   all ASCII. *)
Print Assumptions GoRender.render_file_ascii.
(* §9: the import domain is INTRINSICALLY empty and the renderer STRUCTURALLY consumes [source_imports], so a
   future import constructor forces a renderer update rather than being silently dropped. *)
Print Assumptions GoRender.source_imports_nil.
Print Assumptions GoRender.render_imports_nil_bytes.
Print Assumptions GoRender.render_expr_ascii.
Print Assumptions GoRender.render_const_info_denotes.
Print Assumptions GoRender.render_const_info_denotes_functional.
Print Assumptions GoRender.render_resolved_expr_denotes.
Print Assumptions GoRender.repair_bare_untyped.
Print Assumptions GoRender.repair_bare_not_typed.
Print Assumptions GoRender.repair_uint64_typed.
Print Assumptions GoRender.repair_uint64_max_typed.
(* float rendering: the canonical decimal spelling + conversion spellings; ASCII; the §27 decoder/renderer
   semantic round trip; a bare float denotes its exact rational, a conversion the rounded typed constant. *)
Print Assumptions GoRender.render_float_1p5.
Print Assumptions GoRender.render_float_zero.
Print Assumptions GoRender.render_conv_f32.
Print Assumptions GoRender.render_decimal_ascii.
Print Assumptions GoRender.decode_render_decimal.
Print Assumptions GoRender.render_float_denotes.
Print Assumptions GoRender.render_float_untyped_denotes.
Print Assumptions GoRender.render_conv_f32_typed_denotes.
Print Assumptions GoRender.render_float_untyped_tenth.
Print Assumptions GoRender.render_conv_f64_underflow_zero.
Print Assumptions GoRender.integer_keyword_ascii.
Print Assumptions GoRender.render_int8_127.
Print Assumptions GoRender.render_nested.
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
Print Assumptions GoRender.rb_ff.
Print Assumptions GoRender.rb_nul.
Print Assumptions GoRender.rb_quote.
Print Assumptions GoRender.render_string_denotes.
Print Assumptions GoRender.render_resolved_string_denotes.
(* complex rendering: the exact complex64/complex128 keywords are ASCII; the canonical complex(real, imag)
   literal renders exactly and is ASCII; the INDEPENDENT complex decoder round-trips the canonical spelling
   (§38); the conversion spellings; a bare complex literal denotes its exact ComplexConst (the FUNCTIONAL
   denotation + final resolved root, gated generically above, now cover complex too). *)
Print Assumptions GoRender.complex_keyword_ascii.
Print Assumptions GoRender.render_complex_literal_ascii.
Print Assumptions GoRender.render_cplx_lit.
Print Assumptions GoRender.render_cplx_zero.
Print Assumptions GoRender.render_conv_c64.
Print Assumptions GoRender.render_conv_c128.
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
(* §9 rendering over the standard file map: the rendered map has the SAME key domain as the source; every
   binding is EXACTLY [render_file] of its source; [FilesEqual] sources render to [FM.Equal] maps whose
   CANONICAL transport lists are EQUAL; and the whole [di_transport] is INDEPENDENT of input-node order. *)
Print Assumptions GoEmit.render_map_domain.
Print Assumptions GoEmit.render_map_binding.
Print Assumptions GoEmit.render_map_Equal.
Print Assumptions GoEmit.di_go_file_entries_Equal.
Print Assumptions GoEmit.di_transport_order_independent.

(* GoIndex (Source Forest C2): the PRODUCTION occurrence index over the ONE raw GoProgram grammar — Pillar 1
   (source/index exactness).  The sealed standard positive-key node-table laws; the per-file occurrence-count
   equals the table-free boundary function; and the load-bearing UNIVERSAL per-file source/index exactness
   theorem — the metadata the one-pass builder stores at every local id is EXACTLY the metadata of the exact
   source occurrence there (kind/role/parent/subtree, presence AND absence), against an INDEPENDENT table-free,
   builder-independent source-occurrence specification over the real grammar (file root / package clause /
   declarations / statements / println arguments / conversion operands) — plus its §9 consequences (A..H). *)
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
(* §10 outer-index exactness: the derived outer index [outer_of] (which the sealed [SyntaxIndex]'s internal
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
(* GoIndex §13 typed/kind-refined references: the kind-refiner is sound + complete + mismatch-rejecting, the
   refined kind is the EXACT source occurrence's kind (not a free boolean), and the erased NodeKey determines
   the typed-reference identity. *)
Print Assumptions GoIndex.erase_as_kind.
Print Assumptions GoIndex.as_kind_complete.
Print Assumptions GoIndex.as_kind_mismatch.
Print Assumptions GoIndex.noderefof_kind.
Print Assumptions GoIndex.noderefof_key_inj.
(* GoIndex §21/§22 regressions over the real grammar: println(1,1) — two EQUAL args are DISTINCT occurrences
   (distinct keys/local ids, correct per-arg roles, both recover EInt 1, no dedup); same-shape different-payload
   snapshots have per-snapshot payload recovery yet EQUAL erased index data and NON-interchangeable ref types;
   same-file different-ModuleSpec snapshots have IDENTICAL index data yet NON-interchangeable ref types; and the
   mutation-sensitive fixture pins exact per-occurrence metadata + source views through the UNIVERSAL theorem. *)
Print Assumptions GoIndex.reg_println_1_1.
Print Assumptions GoIndex.reg_payload_a.
Print Assumptions GoIndex.reg_payload_b.
Print Assumptions GoIndex.reg_index_data_equal.
Print Assumptions GoIndex.reg_module_index_equal.
Print Assumptions GoIndex.wf_meta_pkg.
Print Assumptions GoIndex.wf_meta_arg0.
Print Assumptions GoIndex.wf_meta_arg1.
Print Assumptions GoIndex.wf_meta_conv1.
Print Assumptions GoIndex.wf_meta_leaf.
Print Assumptions GoIndex.wf_meta_absent.
Print Assumptions GoIndex.wf_view_pkg.
Print Assumptions GoIndex.wf_view_leaf.
(* GoIndex ROOT-completeness surfaces (§11/§12/§18/§23): FileRef minting soundness + the invalid-path /
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
(* §19 the canonical INDEXED TRAVERSAL: the structural one-pass occurrence fold is EXACT (lists exactly the
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
(* C3 §10 support: [view_expr] is Some exactly for a KExpression occurrence (the dependent SyntaxView). *)
Print Assumptions GoIndex.view_expr_kind.
Print Assumptions GoIndex.kind_view_expr.
(* C3 §4 — the retained IndexedProgram phase boundary: canonical construction reuses exactly the one
   Snap.index_program, and the retained index is the projected field. *)
Print Assumptions GoIndex.index_program_syntax.
Print Assumptions GoIndex.indexed_syntax_proj.
(* C3 §5 — the canonical NodeKey ordered key + standard AVL map: ordered equality, add/find laws, and canonical
   elements as a function of the map's meaning (Equal maps enumerate identically). *)
Print Assumptions GoIndex.nodekey_compare_eq.
Print Assumptions GoIndex.nodekeymap_add_eq.
Print Assumptions GoIndex.nodekeymap_add_neq.
Print Assumptions GoIndex.nodekeymap_elements_Equal.
