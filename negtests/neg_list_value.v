(* EXPECT: non-empty list literal in value position *)
(* A Coq `list` is COMPILE-TIME-ONLY in Fido (a meta-level argument carrier for println /
   slice_of_list / make_chan tags) — it is NOT a runtime Go value.  A non-empty list literal in
   VALUE position would lower to `append(nil, …)`, INVALID Go (append needs a TYPED slice, not an
   untyped `nil`, and the element type is erased).  Extraction MUST abort and direct to
   `slice_of_list <tag> [v1; …]`.  Locks the list-in-value-position fail-closed boundary. *)
From Fido Require Import preamble.
From Fido Require Import GoNumeric.
Require Import Coq.Lists.List. Import ListNotations.
Definition neg_bad : IO (list GoI64) := ret [ (1)%i64 ; (2)%i64 ].
Go Main Extraction neg_out "neg_bad".
