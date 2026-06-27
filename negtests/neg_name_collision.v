(* EXPECT: mangle to the Go identifier *)
(* Two DISTINCT package-level declarations whose Go identifiers collide: Coq `foo'` and `foo_`
   both export to the Go function `Foo_` (apostrophe -> underscore + export-capitalisation).
   Emitting both is a Go `redeclared` error, which `go build` would catch only AFTER extraction —
   TOO LATE (review R7 / the go-build-error-is-too-late tenet).  `register_emitted_name` MUST abort
   at extraction.  This is the PACKAGE-LEVEL half of the identifier-collision class (the per-struct
   FIELD half is neg_field_collision.v).  The two are functions-of-a-param so they emit as named
   Go funcs (not inlined as bare expressions). *)
From Fido Require Import preamble.
Definition foo' (x : GoI64) : GoI64 := i64_add x (1)%i64.
Definition foo_ (x : GoI64) : GoI64 := i64_add x (2)%i64.
Definition neg_bad : IO GoI64 := ret (i64_add (foo' (10)%i64) (foo_ (20)%i64)).
Go Main Extraction neg_out "neg_bad".
