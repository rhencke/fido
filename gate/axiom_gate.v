(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    program-rooted GoProgram -> GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import Ints FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.

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

(* intrinsic GoVersion: the singleton Go1_23 renders EXACTLY "1.23"; decidable equality *)
Print Assumptions GoVersion.render_goversion_go1_23.
Print Assumptions GoVersion.goversion_eqb_eq.

(* the finite map: KEYS ARE NODUP (duplicate keys unrepresentable — the real structural invariant), a
   key-colliding list cannot satisfy the constructor obligation, and lookup is deterministic *)
Print Assumptions FMap.fm_keys_nodup.
Print Assumptions FMap.dup_key_unrepresentable.
Print Assumptions FMap.fm_MapsTo_fun.

(* GoCompile (A) internal exactness: whole-program prog_ok reflects the declarative judgment; go_compile
   sound + complete against it; a rejected program yields no CompilableProgram *)
Print Assumptions GoCompile.prog_ok_iff.
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.reject_no_compile.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.

(* GoRender: all output ASCII; the ROOT correspondence (rendered spelling denotes exactly the value);
   decimal faithfulness + no leading zero; int boundaries; the header is the EXACT first line of a .go
   file; go.mod is rendered from the ModuleSpec — exact bytes (module path + go version in place), header
   first line, all ASCII *)
Print Assumptions GoRender.render_file_ascii.
Print Assumptions GoRender.render_expr_denotes.
Print Assumptions GoRender.print_Z_dec_faithful.
Print Assumptions GoRender.print_Z_pos_no_leading_zero.
Print Assumptions GoRender.render_boundary_max.
Print Assumptions GoRender.render_boundary_min.
Print Assumptions GoRender.render_file_first_line.
Print Assumptions GoRender.render_go_mod_exact.
Print Assumptions GoRender.render_go_mod_first_line.
Print Assumptions GoRender.render_go_mod_ascii.

(* GoEmit: the public emitter requires SafeProgram; the complete image is go.mod + the (possibly empty)
   .go map; the go.mod and every .go file begin with the header first line and are ASCII; on-disk .go
   paths are unique (duplicate paths impossible).  NO nonemptiness claim — the empty program is valid. *)
Print Assumptions GoEmit.render_program_go_mod_header.
Print Assumptions GoEmit.render_program_go_mod_ascii.
Print Assumptions GoEmit.render_program_header.
Print Assumptions GoEmit.render_program_ascii.
Print Assumptions GoEmit.render_image_keys_nodup.
