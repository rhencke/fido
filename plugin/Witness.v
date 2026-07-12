(** The minimal end-to-end witness: a proved SafeProgram for `println(true)`, emitted to a
    real main.go by the Fido Emit transport plugin.  Integration evidence only — the proof
    obligations are discharged in the Fido theory; this file just wires a certified value to
    the writer.  A bad candidate could not construct [demo] (no SafeProgram) and so could not
    reach the emit command. *)
From Stdlib Require Import List.
From Fido Require Import GoAST GoCompile GoSafe GoEmit.
Import ListNotations.

Definition demo_raw : GoFile :=
  mkGoFile main_ident (mkGoFunc main_ident [ SCall println_ident [ EIdent true_ident ] ]).

(* [go_compile] decides admissibility by computation; soundness lifts it to the relation. *)
Lemma demo_compiles : CompilesFile demo_raw (mkCompiledFile [ CPrintln [ CBool true ] ]).
Proof. apply go_compile_sound. reflexivity. Qed.

Definition demo : SafeProgram := certify demo_raw _ demo_compiles.

Declare ML Module "fido.emit".
Fido Emit (emit_directory demo) To "/workspace/e2e-out".
