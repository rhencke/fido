(** Negative fixtures for the TYPE guard (step 1 of the ONE provenance-guarded transport `decode_guarded`).
    `Fido Materialize` (the sole Rocq transport vernac after removed the public `Fido Emit`) applies the
    exact GoEmit.di_transport projection to its argument and typechecks the result, so a forged transport (a
    raw list/pair that never came from render_program of a SafeProgram) has the wrong type and is rejected
    BEFORE any filesystem effect.  Each `Fail` below asserts the command errors.  The COMPLEMENTARY guard —
    a same-typed image whose provenance proof is an axiom/variable — is covered by the TRANSIENTLY-generated
    forged-image fixtures in the emit stage, which additionally reason-check the rejection and that no
    target directory is created. *)
From Stdlib Require Import List String.
From Fido Require Import GoEmit.
Import ListNotations.

Declare ML Module "fido.emit".

(* THE decisive case: a raw transport of the EXACT decodable final shape — a (go.mod bytes, entries) pair
   with generated-looking bytes — that never came from render_program.  If the TYPE guard were bypassed,
   [decode_transport] would happily decode this and install forged content; the guard rejects it because it
   is not a DirectoryImage (di_transport expects one), BEFORE any filesystem effect. *)
Fail Fido Materialize
  (("// fido generated.  do not edit."%string,
    cons ("main.go"%string, "// fido generated.  do not edit."%string) (@nil (string * string)))
   : string * list (string * string))
  To "/workspace/e2e-neg".

(* a raw entries list of the wrong (non-pair) shape — type list (string*string), NOT a DirectoryImage *)
Fail Fido Materialize (@nil (string * string)) To "/workspace/e2e-neg".
Fail Fido Materialize (cons ("main.go"%string, "evil bytes"%string) (@nil (string * string)))
  To "/workspace/e2e-neg".

(* a bare string — not even transport-shaped *)
Fail Fido Materialize "not an image"%string To "/workspace/e2e-neg".
