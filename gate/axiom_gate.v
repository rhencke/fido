(** THE ONE assumptions gate — the sole Print-Assumptions target, compiled fresh EVERY build against the
    dune-built .vo so a warm cache can never skip it.  The build asserts BOTH zero 'Axioms:' lines AND
    exactly as many 'Closed under the global context' lines as there are 'Print Assumptions' commands here
    (an empty/partial log FAILS — fail-closed both ways).  These are the public surfaces of the
    GoAST -> GoCompile -> GoSafe -> GoRender -> GoEmit architecture. *)
From Fido Require Import TargetConfig Literals GoIdent GoAST GoCompile GoSafe GoRender GoEmit.

(* target authority — the pinned facts GoCompile consumes *)
Print Assumptions TargetConfig.int_min_val.
Print Assumptions TargetConfig.int_max_val.
Print Assumptions TargetConfig.println_supported.

(* validated identifiers: equality reduces to the payload (used by erasure) *)
Print Assumptions GoIdent.goident_payload_eq.

(* GoCompile: the declarative authority — an executable elaborator proved SOUND and COMPLETE
   against the relation (not a bare boolean), DETERMINISTIC, and its output ERASES back to the
   raw tree; and the judgment is decidable *)
Print Assumptions GoCompile.go_compile_sound.
Print Assumptions GoCompile.go_compile_complete.
Print Assumptions GoCompile.CompilesFile_det.
Print Assumptions GoCompile.compiled_erases_to_raw.
Print Assumptions GoCompile.GoCompile_dec.

(* GoSafe: safety is a proved property of the operational semantics (no panic), and the
   certificate erases to its raw source *)
Print Assumptions GoSafe.fragment_never_panics.
Print Assumptions GoSafe.sp_erases.

(* GoRender: the direct printer is faithful (string escaping is invertible) and all-ASCII *)
Print Assumptions GoRender.escape_faithful.
Print Assumptions GoRender.render_all_ascii.

(* GoEmit: the DirectoryImage is path-safe (relative, no traversal, .go, unique) and complete *)
Print Assumptions GoEmit.path_ok_main_go.
Print Assumptions GoEmit.emit_paths_ok.
Print Assumptions GoEmit.emit_nonempty.
Print Assumptions GoEmit.emit_unique_paths.
