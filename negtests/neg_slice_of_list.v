(* EXPECT: slice_of_list of a non-literal *)
(* [slice_of_list] of a RUNTIME (non-literal) list — only a statically-known element list
   is modeled; emitting `[]T(nil)` would silently DISCARD the runtime data.  Extraction MUST
   abort (the slice_of_list-nil class). *)
From Fido Require Import preamble.
From Fido Require Import GoSlice.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
Definition neg_bad (xs : list GoI64) : GoSlice GoI64 := slice_of_list TI64 xs.
Go Main Extraction neg_out "neg_bad".
