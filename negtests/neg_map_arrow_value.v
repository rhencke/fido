(* EXPECT: no faithful Go rendering *)
(* Renderability fixture: MapKeysOk gates the map KEY, NOT the value's renderability, so
   [map_make_typed TI64 (TArrow TI64 TI64)] passes the gate — but a func-valued map [map[int64]func(int64)int64]
   is LEGAL Go the plugin does NOT render ([go_type_of_tag (TArrow ..) = None]).  Extraction MUST abort
   (fail-loud INCOMPLETENESS: a valid Go type conservatively rejected, not silently mis-emitted).  Pins that
   MapKeysOk is not a renderability certificate. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoMap.
From Fido Require Import GoEffects.
Definition neg_bad : IO unit := bind (map_make_typed TI64 (TArrow TI64 TI64) eq_refl) (fun _ => ret tt).
Go Main Extraction neg_out "neg_bad".
