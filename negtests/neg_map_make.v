(* EXPECT: bare (unapplied) map constructor *)
(* The UNTYPED `map_make` — it would lower to `make(map[any]any)`, losing the key/value
   types (reads yield `any`, not assignable to `map[K]V`).  Extraction MUST abort, directing
   to `map_make_typed <keytag> <valtag>` (the typed-map rule). *)
From Fido Require Import preamble.
From Fido Require Import GoMap.
From Fido Require Import GoEffects.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
Definition neg_bad : IO (GoMap GoI64 GoI64) := map_make.
Go Main Extraction neg_out "neg_bad".
