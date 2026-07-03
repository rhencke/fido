(* EXPECT: export to the SAME Go field name *)
(* Two record projections that differ ONLY by mangling — Coq `x'` and `x_` both export to
   the Go field `X_` (apostrophe -> underscore + export-capitalisation).  The emitted struct
   would have a DUPLICATE field `X_` — invalid Go.  Relying on `go build` to catch a duplicate
   field is TOO LATE (the name-injectivity class): extraction MUST abort.
   This is the field-namespace half of the identifier-collision class (the package-level half
   is `register_emitted_name`); neither had a negative fixture before. *)
From Fido Require Import preamble.
Record Pt := { x' : GoI64 ; x_ : GoI64 }.
Definition mk : Pt := {| x' := (1)%i64 ; x_ := (2)%i64 |}.
Definition neg_bad : IO GoI64 := ret (x' mk).
Go Main Extraction neg_out "neg_bad".
