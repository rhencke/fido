(* EXPECT: non-literal list *)
(* `println`/`print` lower by UNFOLDING the argument list to its statically-known elements
   (each boxed `any` value becomes one Go print operand).  A NON-literal list — here the
   parameter `l`, whose elements are not known at extraction — cannot be unfolded, so the
   backend MUST abort ("println of a non-literal list (only statically-known argument lists
   are modeled)") rather than emit a plausible-but-wrong call.  Locks the [print|println]
   `unfold_list = None` fail-closed site. *)
From Fido Require Import preamble.
From Fido Require Import GoEffects.
From Fido Require Import GoRuntimeTypes.
Definition neg_bad (l : list GoAny) : IO unit := println l.
Go Main Extraction neg_out "neg_bad".
