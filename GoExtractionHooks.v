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
From Fido Require Import GoEffects.
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

(** EMISSION-ONLY marker for the STATIC-TARGET CFG class ([GoCFG.CBlock]): the terminators
    are constructor SYNTAX ([CBSeq]/[CBIf]), so the plugin lowers the structure without
    recognizing computed [Next] values, and a demo's admissibility arrives ALREADY DECIDED
    by GoCFG's checkers ([check_targets]/[check_forward] — [eq_refl] gate lemmas at the
    call site).  Model-side semantics live in GoCFG ([cblock_denote] under
    [blocks_eval]/[blocks_diverge]) — never this marker. *)
Definition run_cblocks (start : nat) (cbs : list CBlock) : IO unit :=
  fun w => OPanic (anyt TString "fido: run_cblocks is EMISSION-ONLY — the CBlock semantics are GoCFG's cblock_denote under blocks_eval/blocks_diverge, never evaluation"%string) w.

(** The marker can never be mistaken for normal completion. *)
Lemma run_cblocks_never_ret : forall start cbs (w w' : World),
  run_io (run_cblocks start cbs) w <> ORet tt w'.
Proof. intros start cbs w w'. cbn. discriminate. Qed.

(** [defer_call] — Go's func-scoped [defer], lowered BY NAME by the plugin; the shallow sequential
    [run_io] semantics CANNOT reify a func-scoped deferred command, so the model body is a LOUD
    panic guard (never a silent drop).  The faithful semantics is [run_cmd]'s [CDfr] (cmd.v).
    A hook guard is not a certified semantic definition — that is why it lives HERE (CLAUDE.md,
    CFG law). *)
Definition defer_call (_ : IO unit) : IO unit :=
  fun w => OPanic (anyt TString "fido: defer_call has no shallow run_io meaning — a func-scoped defer needs the deep command model; the faithful semantics is run_cmd's CDfr (cmd.v); run_io fails loud rather than silently dropping the deferred effect"%string) w.
