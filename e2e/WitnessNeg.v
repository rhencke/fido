(** Negative fixtures for the TYPE guard (step 1 of the emit boundary).  `Fido Emit` applies the exact
    GoEmit.directory_entries projection to its argument and typechecks the result, so a forged transport
    (a raw list that never came from render_program of a SafeProgram) has the wrong type and is rejected
    BEFORE any filesystem effect.  Each `Fail` below asserts the command errors.  The COMPLEMENTARY guard —
    a same-typed image whose provenance proof is an axiom/variable — is covered by WitnessForge{,Opaque,
    Var}.v, which additionally reason-check the rejection and that no target directory is created. *)
From Stdlib Require Import List String.
From Fido Require Import GoEmit.
Import ListNotations.

Declare ML Module "fido.emit".

(* a raw empty transport list — type list (string*string), NOT a DirectoryImage: rejected *)
Fail Fido Emit (@nil (string * string)) To "/workspace/e2e-neg".

(* a raw singleton with arbitrary bytes — would install forged content if accepted: rejected *)
Fail Fido Emit (cons ("main.go"%string, "evil bytes"%string) (@nil (string * string)))
  To "/workspace/e2e-neg".

(* a bare string — not even list-shaped: rejected *)
Fail Fido Emit "not an image"%string To "/workspace/e2e-neg".
