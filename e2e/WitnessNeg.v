(** Negative fixtures for the type guard: a forged transport is rejected before any filesystem effect. *)
From Stdlib Require Import List String.
From Fido Require Import Emit.
Import ListNotations.

Declare ML Module "fido.emit".

(* the decisive case: the exact decodable final shape, which the type guard still rejects *)
Fail Fido Materialize
  (("// fido was here.  woof woof.  do not edit."%string,
    cons ("main.go"%string, "// fido was here.  woof woof.  do not edit."%string) (@nil (string * string)))
   : string * list (string * string))
  To "/workspace/e2e-neg".

(* a raw entries list of the wrong shape *)
Fail Fido Materialize (@nil (string * string)) To "/workspace/e2e-neg".
Fail Fido Materialize (cons ("main.go"%string, "evil bytes"%string) (@nil (string * string)))
  To "/workspace/e2e-neg".

(* a bare string — not even transport-shaped *)
Fail Fido Materialize "not an image"%string To "/workspace/e2e-neg".
