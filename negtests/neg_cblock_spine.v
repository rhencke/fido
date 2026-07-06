(* EXPECT: suppressed model/hook name run_cblocks *)
(* run_cblocks over an OPAQUE spine (a function parameter, not a literal [cb0; …]).
   Extraction MUST abort: a computed spine has no static structure — lowering a guess
   would emit a DIFFERENT program's control flow.  This shape survives the optimizer as a
   value-position reference to the suppressed hook, so the SUPPRESSION SEAL rejects it
   (the arm's own "non-literal block-list spine" rejection covers directly-applied
   computed spines; the oob fixture pins the arm's target validation). *)
From Fido Require Import preamble.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoCFG.
From Fido Require Import GoExtractionHooks.
Require Import Coq.Lists.List.
Import ListNotations.
Definition neg_bad (cbs : list CBlock) : IO unit :=
  bind (println [any (int_lit 0 eq_refl)]) (fun _ => run_cblocks 0%nat cbs).
Go Main Extraction neg_out "neg_bad".
