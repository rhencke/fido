(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    program-rooted GoProgram -> GoTypes (the one type authority: untyped GoConst resolved through
    {TBool, the integer family TInteger over IntegerType, the float family TFloat over FloatType, TString} to
    ProgramTyped over the same AST) ->
    GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import Ints Floats FilePath FMap ModulePath GoVersion GoAST GoTypes GoCompile GoSafe GoRender GoEmit.

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

(* the finite map: KEYS ARE NODUP (duplicate keys unrepresentable — the real structural invariant), a
   key-colliding list cannot satisfy the constructor obligation, and lookup is deterministic *)
Print Assumptions FMap.fm_keys_nodup.
Print Assumptions FMap.dup_key_unrepresentable.
Print Assumptions FMap.fm_MapsTo_fun.

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
Print Assumptions GoTypes.cplx_scar_direct_vs_nested.
Print Assumptions GoTypes.cplx_scar_imag_direct_vs_nested.
Print Assumptions GoTypes.cplx_underflow_pos_zero.

(* GoCompile (A) internal exactness: whole-program prog_ok reflects the declarative judgment; go_compile
   sound + complete against it; a rejected program yields no CompilableProgram; the compiled evidence exposes
   that the same program is typed; the empty program is accepted; a concrete integer-family program compiles;
   an out-of-range and an invalid-nested-conversion program are rejected with the honest typing error (and
   have no CompilableProgram); a concrete string program compiles. *)
Print Assumptions GoCompile.prog_ok_iff.
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
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
   integer / string / integer-conversion / bare float / float-conversion recognisers are pairwise disjoint, so
   no spelling admits two conflicting constant statuses) and the final
   resolved root (resolved argument -> const-status + well-formed value of its resolved type carrying the same
   constant); the §4 integer-repair regressions (a bare integer above int_max stays UNTYPED, does NOT denote a
   typed int, and only an explicit uint64 conversion assigns the type); the ten integer keywords are ASCII;
   the exact conversion spellings; decimal faithfulness + no leading zero; int boundaries; the header is the
   EXACT first line of a .go file; go.mod is rendered from the ModuleSpec — exact bytes, header first line,
   all ASCII. *)
Print Assumptions GoRender.render_file_ascii.
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
