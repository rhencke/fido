(* EXPECT: NON-COMPARABLE key type *)
(* A map with a NON-comparable key type (a slice) — Go forbids slice/map/func map keys
   (`invalid map key type`).  Extraction MUST abort rather than emit `make(map[[]T]V)`
   (the map-key comparability rule). *)
From Fido Require Import preamble.
From Fido Require Import GoMap.
From Fido Require Import GoEffects.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
Definition neg_bad : IO (GoMap (GoSlice GoI64) GoI64) := map_make_typed (TSlice TI64) TI64.
Go Main Extraction neg_out "neg_bad".
