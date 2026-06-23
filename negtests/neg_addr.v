(* EXPECT: not provably addressable *)
(* &x of a NON-addressable operand (not a bound variable) — the [ref_as_ptr] MLrel guard.
   Extraction MUST abort: emitting `&(if b then r1 else r2)` is invalid Go (Go forbids `&`
   of a non-addressable expression).  A regression that drops the guard reopens a fail-OPEN
   site (invalid Go at `go build` = too late). *)
From Fido Require Import preamble.
Definition neg_bad (b : bool) (r1 r2 : Ref GoI64) : Ptr GoI64 := ref_as_ptr (if b then r1 else r2).
Go Main Extraction neg_out "neg_bad".
