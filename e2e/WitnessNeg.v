(** Negative fixtures: the `Fido Emit` command enforces DirectoryImage PROVENANCE at the boundary.  It
    applies the exact GoEmit.directory_entries projection to its argument and typechecks the result, so a
    forged transport (a raw list that never came from render_program of a SafeProgram) is rejected BEFORE
    any filesystem effect.  Each `Fail` below asserts the command errors; the emit stage additionally
    asserts the target directory was never created. *)
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
