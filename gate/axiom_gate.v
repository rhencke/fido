(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    program-rooted GoProgram -> GoTypes (the one type authority: untyped GoConst resolved through
    {TBool,TInt,TString} to ProgramTyped over the same AST) -> GoCompile -> GoSafe -> GoRender -> GoEmit
    architecture. *)
From Fido Require Import Ints FilePath FMap ModulePath GoVersion GoAST GoTypes GoCompile GoSafe GoRender GoEmit.

(* the 64-bit integer authority (only the constants an admitted construct uses) *)
Print Assumptions Ints.int_min_val.
Print Assumptions Ints.int_max_val.

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

(* GoTypes — the ONE Go type authority (EVIDENCE over the raw AST): zero-sign constant equality; default-
   type exactness; representability reflection (the single 64-bit range decision); expression resolution
   sound + complete + deterministic; statement + program typing reflection; int max/min accepted;
   overflow/underflow rejected. *)
Print Assumptions GoTypes.const_value_zero_sign.
Print Assumptions GoTypes.const_default_type_int.
Print Assumptions GoTypes.const_representableb_iff.
Print Assumptions GoTypes.resolve_expr_sound.
Print Assumptions GoTypes.resolve_expr_complete.
Print Assumptions GoTypes.resolve_expr_deterministic.
Print Assumptions GoTypes.stmt_typedb_iff.
Print Assumptions GoTypes.program_typedb_iff.
Print Assumptions GoTypes.res_int_max.
Print Assumptions GoTypes.res_int_min.
Print Assumptions GoTypes.res_over.
Print Assumptions GoTypes.res_under.
Print Assumptions GoTypes.empty_program_typed.
Print Assumptions GoTypes.bool_not_resolve_int.
Print Assumptions GoTypes.int_not_resolve_bool.
(* strings: default type TString; an arbitrary-byte string resolves as TString; a string does NOT resolve as
   bool/int and no bool/int const is representable as TString (cross-type rejection); a mixed bool/int/string
   println statement is typed *)
Print Assumptions GoTypes.const_default_type_string.
Print Assumptions GoTypes.res_str_bytes.
Print Assumptions GoTypes.str_not_resolve_bool.
Print Assumptions GoTypes.str_not_resolve_int.
Print Assumptions GoTypes.cstr_not_bool.
Print Assumptions GoTypes.cstr_not_int.
Print Assumptions GoTypes.stmt_mixed_str_typed.
Print Assumptions GoTypes.str_representable.
Print Assumptions GoTypes.str_representableb.

(* GoCompile (A) internal exactness: whole-program prog_ok reflects the declarative judgment (now rooted
   in the GoTypes typing authority); go_compile sound + complete against it; a rejected program yields no
   CompilableProgram; the compiled evidence exposes that the same program is typed; the empty program is
   accepted under the new typing authority *)
Print Assumptions GoCompile.prog_ok_iff.
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.reject_no_compile.
Print Assumptions GoCompile.compilable_program_typed.
Print Assumptions GoCompile.prog_ok_empty.
(* a concrete string program is whole-program admissible (typed + compiles to a CompilableProgram) *)
Print Assumptions GoCompile.str_program_ok.
Print Assumptions GoCompile.str_program_compiles.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree; a resolved expression
   evaluates to a value of the resolved GoType (one type authority across compiler and runtime) *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.
Print Assumptions GoSafe.eval_expr_resolved_type.
(* the string value type: a string literal evaluates to the EXACT runtime byte sequence, of type TString *)
Print Assumptions GoSafe.eval_string_value.
Print Assumptions GoSafe.eval_string_type.
Print Assumptions GoSafe.eval_string_resolved_type.

(* GoRender: all output ASCII; the ROOT correspondence (rendered spelling denotes exactly the value);
   decimal faithfulness + no leading zero; int boundaries; the header is the EXACT first line of a .go
   file; go.mod is rendered from the ModuleSpec — exact bytes (module path + go version in place), header
   first line, all ASCII *)
Print Assumptions GoRender.render_file_ascii.
Print Assumptions GoRender.render_expr_denotes.
Print Assumptions GoRender.render_resolved_expr_denotes.
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

(* GoEmit: the public emitter requires SafeProgram; the complete image is go.mod + the (possibly empty)
   .go map; the go.mod and every .go file begin with the header first line and are ASCII; on-disk .go
   paths are unique (duplicate paths impossible).  NO nonemptiness claim — the empty program is valid. *)
Print Assumptions GoEmit.render_program_go_mod_header.
Print Assumptions GoEmit.render_program_go_mod_ascii.
Print Assumptions GoEmit.render_program_header.
Print Assumptions GoEmit.render_program_ascii.
Print Assumptions GoEmit.render_image_keys_nodup.
