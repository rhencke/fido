(* EXPECT: out of range *)
(* run_cblocks with a literal Jump PAST the block list.  Extraction MUST abort: the goto
   label would be undefined Go (fail-open at go build = too late).  The model-side gate
   [check_targets] already rejects this CFG — the plugin mirrors it fail-closed. *)
From Fido Require Import preamble.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoCFG.
From Fido Require Import GoExtractionHooks.
Require Import Coq.Lists.List.
Import ListNotations.
Definition neg_bad : IO unit :=
  run_cblocks 0%nat [ CBSeq (println [any (int_lit 1 eq_refl)]) (Jump 5%nat) ].
Go Main Extraction neg_out "neg_bad".
