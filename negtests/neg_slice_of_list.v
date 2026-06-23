(* EXPECT: slice_of_list of a non-literal *)
(* [slice_of_list] of a RUNTIME (non-literal) list — only a statically-known element list
   is modeled; emitting `[]T(nil)` would silently DISCARD the runtime data.  Extraction MUST
   abort (backend P0 #4, the slice_of_list-nil class). *)
From Fido Require Import preamble.
Definition neg_bad (xs : list GoI64) : GoSlice GoI64 := slice_of_list TI64 (List.rev xs).
Go Main Extraction neg_out "neg_bad".
