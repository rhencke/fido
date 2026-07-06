(* EXPECT: suppressed model/hook name run_cblocks *)
(* A bare/partial reference to run_cblocks in value position.  Its declaration is
   SUPPRESSED (the plugin lowers recognized call shapes only), so a surviving reference
   would print an UNDEFINED Go identifier — the pp_expr suppression SEAL must abort
   extraction instead (fail-loud, never at go build).  Computed-spine shapes collapse to
   this class under the optimizer; the arm's own non-literal-spine rejection remains as
   defense-in-depth, and neg_cblock_oob pins the arm's target validation. *)
From Fido Require Import preamble.
From Fido Require Import GoEffects.
From Fido Require Import GoCFG.
From Fido Require Import GoExtractionHooks.
Definition neg_bad : nat -> list CBlock -> IO unit := run_cblocks.
Go Main Extraction neg_out "neg_bad".
