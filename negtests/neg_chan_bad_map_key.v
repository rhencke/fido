(* EXPECT: NON-COMPARABLE map key *)
(* The trusted plugin RENDERS [GoTypeTag] terms independently of [GoMap.map_make_typed]'s [MapKeysOk]
   gate, so an invalid nested map tag can reach a NON-map allocator.  Here [make_chan (TMap (TSlice TI64) TI64)]
   would emit [make(chan map[[]int64]int64)] — Go rejects a SLICE map key — a fail-OPEN.  [go_type_of_tag]'s
   map-key comparability check (every [TMap] node) makes the renderer FAIL LOUD instead, so extraction MUST
   abort.  This pins that an invalid nested map key cannot reach an emitted type path via [make_chan]. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoSlice.
From Fido Require Import GoMap.
From Fido Require Import GoChan.
From Fido Require Import GoEffects.
Definition neg_bad : IO unit :=
  bind (make_chan (TMap (TSlice TI64) TI64)) (fun _ => ret tt).
Go Main Extraction neg_out "neg_bad".
