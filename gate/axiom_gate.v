(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the one-AST
    GoAST -> GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import TargetConfig GoAST GoCompile GoSafe GoRender GoEmit.

(* target authority — the pinned facts GoCompile consumes *)
Print Assumptions TargetConfig.int_min_val.
Print Assumptions TargetConfig.int_max_val.
Print Assumptions TargetConfig.println_supported.

(* GoCompile: exact static admissibility over the ONE AST — executable decision SOUND and COMPLETE
   against the declarative judgment (never a boolean), and decidable *)
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.go_compile_iff.
Print Assumptions GoCompile.GoCompile_dec.

(* GoSafe: exact VALUE semantics — a zero literal and a negated zero agree *)
Print Assumptions GoSafe.eval_zero_sign_agnostic.

(* GoRender: all output is ASCII; the emitted decimal denotes exactly the value and never has an
   illegal leading zero (no octal reinterpretation) *)
Print Assumptions GoRender.render_all_ascii.
Print Assumptions GoRender.print_Z_dec_faithful.
Print Assumptions GoRender.print_Z_pos_no_leading_zero.

(* GoEmit: the image is exactly one file, the fixed relative main.go, and is nonempty *)
Print Assumptions GoEmit.emit_is_single_main_go.
Print Assumptions GoEmit.emit_nonempty.
