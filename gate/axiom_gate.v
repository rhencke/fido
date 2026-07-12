(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the program-rooted
    GoProgram -> GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import Ints FMap GoAST GoCompile GoSafe GoRender GoEmit.

(* the 64-bit integer authority *)
Print Assumptions Ints.int_min_val.
Print Assumptions Ints.int_max_val.
Print Assumptions Ints.uint_max_val.

(* the finite map: duplicate keys are unrepresentable (deterministic lookup) *)
Print Assumptions FMap.fm_MapsTo_fun.

(* GoCompile (A) internal checker exactness (prog_ok <-> the judgment; go_compile proof-producing,
   sound + complete); a rejected program yields no CompilableProgram; boundary/rejection facts;
   duplicate paths unrepresentable *)
Print Assumptions GoCompile.prog_ok_iff.
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.reject_no_compile.
Print Assumptions GoCompile.accept_max_int.
Print Assumptions GoCompile.accept_min_int.
Print Assumptions GoCompile.reject_pos_overflow.
Print Assumptions GoCompile.reject_neg_overflow.
Print Assumptions GoCompile.path_unique.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.

(* GoRender: all output ASCII; decimal denotes exactly the value + no leading zero; the rendered
   literal denotes exactly the value (bool/int/neg + int boundaries); every file has the header *)
Print Assumptions GoRender.render_file_ascii.
Print Assumptions GoRender.print_Z_dec_faithful.
Print Assumptions GoRender.print_Z_pos_no_leading_zero.
Print Assumptions GoRender.render_bool_faithful.
Print Assumptions GoRender.render_int_faithful.
Print Assumptions GoRender.render_neg_faithful.
Print Assumptions GoRender.render_boundary_max.
Print Assumptions GoRender.render_boundary_min.
Print Assumptions GoRender.render_file_header.

(* GoEmit: the public emitter requires SafeProgram; the image keys are the program's paths; every
   emitted file begins with the header and is ASCII; the current fragment emits exactly one file *)
Print Assumptions GoEmit.render_program_keys.
Print Assumptions GoEmit.render_program_header.
Print Assumptions GoEmit.render_program_ascii.
Print Assumptions GoEmit.render_program_one_file.
