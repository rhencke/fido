(* EXPECT: bare (unapplied) map constructor *)
(* The UNTYPED `map_make` — it would lower to `make(map[any]any)`, losing the key/value
   types (reads yield `any`, not assignable to `map[K]V`).  Extraction MUST abort, directing
   to `map_make_typed <keytag> <valtag>` (backend R4(a)). *)
From Fido Require Import preamble.
Definition neg_bad : IO (GoMap GoI64 GoI64) := map_make.
Go Main Extraction neg_out "neg_bad".
