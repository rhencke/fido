(** ==================================================================================================
    GoExtractionHooks — TRUSTED EXTRACTION HOOKS, NOT SEMANTICS.

    Every name in this module exists ONLY because plugin/go.ml lowers it BY NAME at emission
    time (gap #10 — the plugin is trusted and unverified).  Nothing here is a semantic
    authority: the model-side meaning of each hook is a LOUD PANIC, so no proof can mistake a
    hook for behavior, and the semantic story lives entirely in the modules the hook's demos
    point at (for [run_blocks]: GoCFG.v's [blocks_eval]/[blocks_diverge] and the gated
    [blocks_cfg_surface]).  If a hook stops being lowered, it must be DELETED, not kept as a
    pseudo-builtin.  ============================================================================== *)
Require Import Coq.Strings.String.   (* the marker panic message *)
From Fido Require Import GoRuntimeTypes.
From Fido Require Import builtins.
From Fido Require Import GoCFG.

(** EMISSION-ONLY marker (the plugin suppresses this body and emits labels+goto).
    Evaluating the model-side [run_blocks] yields a loud, recognizable panic —
    never a fabricated [Done], never a step-capped approximation. *)
Definition run_blocks (start : nat) (blocks : list (IO Next)) : IO unit :=
  fun w => OPanic (anyt TString "fido: run_blocks is EMISSION-ONLY — model-side CFG semantics are blocks_eval/blocks_diverge, never evaluation"%string) w.

(** The marker can never be mistaken for normal completion. *)
Lemma run_blocks_never_ret : forall start blocks (w w' : World),
  run_io (run_blocks start blocks) w <> ORet tt w'.
Proof. intros start blocks w w'. cbn. discriminate. Qed.
