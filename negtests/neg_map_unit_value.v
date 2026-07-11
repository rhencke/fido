(* EXPECT: no faithful Go rendering *)
(* Renderability fixture: [map_make_typed TI64 TUnit] passes MapKeysOk (the value's renderability is not
   gated), but the plugin has no faithful Go rendering for [TUnit] ([go_type_of_tag TUnit = None] — it does not
   map [unit] to [struct{}]).  Extraction MUST abort.  Pins that MapKeysOk is not a renderability certificate. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoMap.
From Fido Require Import GoEffects.
Definition neg_bad : IO unit := bind (map_make_typed TI64 TUnit eq_refl) (fun _ => ret tt).
Go Main Extraction neg_out "neg_bad".
