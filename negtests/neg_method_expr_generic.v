(* EXPECT: GENERIC-receiver method used as a bare value *)
(* A generic-receiver method ([nbox_get]) used BARE in argument position — the exact
   shape the CONCRETE method expression supports ([apply_pt sum_coords] ->
   [Point.Sum_coords]).  Go's method expression needs a CONCRETE instantiation
   ([NBox[int64].M]) that the erased MiniML type does not carry.  Extraction MUST
   abort; a regression would emit the unbound [NBox.Nbox_get] (invalid Go at
   `go build` = too late). *)
From Fido Require Import preamble.
Record NBox (A : Type) := MkNBox { nval : A ; ntag : GoI64 }.
Arguments MkNBox {A}. Arguments nval {A}. Arguments ntag {A}.
Definition nbox_get {A : Type} (b : NBox A) : A := nval b.
Extraction NoInline nbox_get.
Definition apply_nb (f : NBox GoI64 -> GoI64) (b : NBox GoI64) : GoI64 := f b.
Extraction NoInline apply_nb.
Definition neg_bad (b : NBox GoI64) : GoI64 := apply_nb (@nbox_get GoI64) b.
Go Main Extraction neg_out "neg_bad".
