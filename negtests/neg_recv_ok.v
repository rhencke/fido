(* EXPECT: recv_ok) used in expression position *)
(* [recv_ok] used as a VALUE (expression position) — its continuation (`fun x ok => …`)
   cannot be emitted as a value and would be SILENTLY DROPPED.  Extraction MUST abort
   (the dropped-continuation class). *)
From Fido Require Import preamble.
From Fido Require Import GoEffects.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoNumeric.
Definition neg_h (x : GoI64) (ok : bool) : IO unit := ret tt.
Definition neg_bad (ch : GoChan GoI64) : IO unit := recv_ok TI64 ch neg_h.
Go Main Extraction neg_out "neg_bad".
