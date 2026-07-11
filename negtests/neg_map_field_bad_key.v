(* EXPECT: pp_type path *)
(* Pins the [pp_type] map-key guard (plugin/go.ml, the [is_go_map_type] arm) — the ONE map-key renderer
   [neg_chan_bad_map_key] does NOT reach (that fixture pins [go_type_of_tag]).  A record wrapping a [GoMap]
   renders as a DEFINED TYPE over the map ([type Counts map[string]int64] in main.v), so a bad-key field type
   [GoMap (GoSlice GoI64) GoI64] makes the plugin emit [type ... map[[]int64]int64] — a SLICE map key, which Go
   rejects.  The [pp_type_comparable_key] guard must FAIL LOUD ("... (pp_type path)") instead.  The bad-key map
   VALUE is built with the PUBLIC [map_empty] (= [MkMap 0]) — [map_make_typed] can't build it (its MapKeysOk
   proof is [false]).  Extraction MUST abort. *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
From Fido Require Import GoSlice.
From Fido Require Import GoMap.
From Fido Require Import GoEffects.
Record Bad := MkBad { b_val : GoMap (GoSlice GoI64) GoI64 ; b_tag : GoTypeTag (GoMap (GoSlice GoI64) GoI64) }.
Definition mk_bad (m : GoMap (GoSlice GoI64) GoI64) : Bad := MkBad m (TMap (TSlice TI64) TI64).
Definition b_size (c : Bad) : IO GoInt := map_len (TSlice TI64) TI64 (b_val c).
Definition neg_bad : IO unit :=
  bind (b_size (mk_bad (@map_empty (GoSlice GoI64) GoI64))) (fun _ => ret tt).
Go Main Extraction neg_out "neg_bad".
