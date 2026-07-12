(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the collapsed
    GoAST -> GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import TargetConfig Literals GoIdent GoAST GoCompile GoSafe GoRender GoEmit.

(* target authority *)
Print Assumptions TargetConfig.int_min_val.
Print Assumptions TargetConfig.int_max_val.
Print Assumptions TargetConfig.println_supported.

(* admitted literal forms + target representability *)
Print Assumptions Literals.int_lit_ok_in_range.
Print Assumptions Literals.neg_lit_ok_in_range.
Print Assumptions Literals.int_lit_ok_range.
Print Assumptions Literals.neg_lit_ok_range.

(* validated identifiers *)
Print Assumptions GoIdent.goident_payload_eq.
Print Assumptions GoIdent.goident_facts.

(* GoCompile: exact static admissibility — the executable checker is SOUND and COMPLETE
   against the declarative judgment (not a bare boolean equality), and the judgment is decidable *)
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.go_compile_iff.
Print Assumptions GoCompile.GoCompile_dec.

(* GoEmit: the DirectoryImage is path-safe (relative, no traversal, .go, unique) and complete *)
Print Assumptions GoEmit.path_ok_main_go.
Print Assumptions GoEmit.emit_paths_ok.
Print Assumptions GoEmit.emit_nonempty.
Print Assumptions GoEmit.emit_unique_paths.
