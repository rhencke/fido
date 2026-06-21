(** * Verified relooping — a first slice of plugin gap #10.

    Fido's extraction plugin lowers a CONTROL-FLOW GRAPH (basic blocks + conditional gotos — the
    "goto-CFG substrate" that [select]/[defer] also factor onto) into STRUCTURED Go control flow
    (if/for/break).  That lowering — the relooper — is the most intricate, most error-prone part of
    the (trusted, UNVERIFIED) plugin: nothing today relates the structured Go it emits to the CFG it
    started from (PROGRESS.md gap #10).

    This file is the FIRST VERIFIED SLICE of that relationship, done entirely in Rocq: a CFG with a
    real operational semantics, a structured target with its semantics, and a proof that the lowering
    is SEMANTICS-PRESERVING.  It is a *reference* model — it does NOT verify the OCaml plugin itself
    (that needs reflecting the OCaml into Rocq), but it establishes that the transformation CAN be
    verified, gives the correctness method (compositional "realizes" combinators), and is a spec the
    plugin can eventually be checked against.

    SCOPE (honest): (1) ACYCLIC CFGs lowered to nested if/seq, with the join block DUPLICATED into both
    branches (semantically correct; the plugin's no-duplication relooping is an optimisation atop this
    correctness core) — the [Realizes] combinators + [diamond_realized].  (2) CYCLIC CFGs → structured
    LOOPS (the genuinely hard part): a relational [seval] with [LLoop]/[LBreak], and [while_realized] —
    the canonical while-loop CFG (with a back-edge) lowered to [loop { … break }], proved
    semantics-preserving by INDUCTION ON THE [cfg_halts] DERIVATION (the loop-iteration count).
    Both axiom-free.  STILL OPEN: a GENERAL relooper FUNCTION over arbitrary (reducible) CFGs — these
    are the two correctness cores (straight-line + single loop) it would be built from.  Proof-only:
    emits no Go. *)

From Stdlib Require Import List Lia Arith.
Import ListNotations.

Section Relooper.

(** The block-local computation is abstract: a block transforms an opaque [State], and conditions
    observe it.  The relooper is about CONTROL FLOW, so the data is a parameter. *)
Variable State : Type.

(** A block's terminator: return/halt, an unconditional goto, or a conditional branch to two blocks
    (condition evaluated AFTER the block body has run, exactly as a real basic block ends). *)
Inductive Term : Type :=
  | TRet  : Term
  | TGoto : nat -> Term
  | TIf   : (State -> bool) -> nat -> nat -> Term.

Record Block : Type := mkBlk { blk_body : State -> State ; blk_term : Term }.

(** A CFG maps block ids to blocks. *)
Definition CFG : Type := nat -> Block.

(** Big-step CFG semantics: [cfg_halts g l s sf] — execution that ENTERS block [l] in state [s] runs
    the block body, follows its terminator, and (if it terminates) HALTS with final state [sf].  A
    non-terminating run simply has no derivation (this is partial / total-correctness semantics). *)
Inductive cfg_halts (g : CFG) : nat -> State -> State -> Prop :=
  | ch_ret  : forall l s,
      blk_term (g l) = TRet ->
      cfg_halts g l s (blk_body (g l) s)
  | ch_goto : forall l l' s sf,
      blk_term (g l) = TGoto l' ->
      cfg_halts g l' (blk_body (g l) s) sf ->
      cfg_halts g l s sf
  | ch_if   : forall l c a b s sf,
      blk_term (g l) = TIf c a b ->
      cfg_halts g (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf ->
      cfg_halts g l s sf.

(** The STRUCTURED target (loop-free fragment): run a body, sequence, or branch.  This is the shape
    the plugin emits for acyclic control flow — straight-line Go with nested [if]s. *)
Inductive Stmt : Type :=
  | SBody : (State -> State) -> Stmt
  | SSeq  : Stmt -> Stmt -> Stmt
  | SIf   : (State -> bool) -> Stmt -> Stmt -> Stmt.

(** Structured semantics — TOTAL (the loop-free fragment always terminates), so a plain [Fixpoint]. *)
Fixpoint srun (s0 : Stmt) (s : State) : State :=
  match s0 with
  | SBody f   => f s
  | SSeq a b  => srun b (srun a s)
  | SIf c a b => if c s then srun a s else srun b s
  end.

(** [Realizes g S l]: the structured program [S] computes, on EVERY input state, exactly the final
    state the CFG produces when entered at block [l].  This is soundness of the lowering of block [l]. *)
Definition Realizes (g : CFG) (S : Stmt) (l : nat) : Prop :=
  forall s, cfg_halts g l s (srun S s).

(** ── The CORRECTNESS COMBINATORS — one per terminator shape.  They compose: a structured program
    for the whole CFG is BUILT bottom-up from the terminators, and each step is sound by these. ── *)

(** A [TRet] block lowers to just its body. *)
Lemma realize_ret : forall g l,
  blk_term (g l) = TRet -> Realizes g (SBody (blk_body (g l))) l.
Proof. intros g l Ht s. cbn. apply ch_ret. exact Ht. Qed.

(** A [TGoto l'] block lowers to its body SEQUENCED before the structured code for [l']. *)
Lemma realize_goto : forall g l l' S,
  blk_term (g l) = TGoto l' -> Realizes g S l' ->
  Realizes g (SSeq (SBody (blk_body (g l))) S) l.
Proof.
  intros g l l' S Ht HR s. cbn.
  eapply ch_goto; [exact Ht | exact (HR (blk_body (g l) s))].
Qed.

(** A [TIf c a b] block lowers to its body SEQUENCED before an [SIf] over the two branch programs.
    The shared join block is DUPLICATED into [Sa] and [Sb] (whoever built them) — correct, since the
    join runs after either branch regardless. *)
Lemma realize_if : forall g l c a b Sa Sb,
  blk_term (g l) = TIf c a b -> Realizes g Sa a -> Realizes g Sb b ->
  Realizes g (SSeq (SBody (blk_body (g l))) (SIf c Sa Sb)) l.
Proof.
  intros g l c a b Sa Sb Ht HRa HRb s. cbn.
  eapply ch_if; [exact Ht |]. cbn.
  destruct (c (blk_body (g l) s)) eqn:E.
  - exact (HRa (blk_body (g l) s)).
  - exact (HRb (blk_body (g l) s)).
Qed.

(** ── WITNESS: the IF-DIAMOND, the canonical reducible-but-non-trivial CFG. ──
    block 0: run [b0], branch on [c] to 1 or 2;  block 1: run [b1], goto 3;
    block 2: run [b2], goto 3;  block 3 (join): run [b3], return.
    The relooper LOWERS it (join duplicated) to:  b0 ; if c { b1 ; b3 } else { b2 ; b3 }.
    [diamond_realized] proves that structured program computes EXACTLY the CFG — built purely from the
    three combinators, so the proof scales to any acyclic CFG by the same recipe. *)
Definition diamond (b0 b1 b2 b3 : State -> State) (c : State -> bool) : CFG :=
  fun l => match l with
           | 0 => mkBlk b0 (TIf c 1 2)
           | 1 => mkBlk b1 (TGoto 3)
           | 2 => mkBlk b2 (TGoto 3)
           | _ => mkBlk b3 TRet
           end.

Theorem diamond_realized : forall b0 b1 b2 b3 c,
  Realizes (diamond b0 b1 b2 b3 c)
    (SSeq (SBody b0)
          (SIf c (SSeq (SBody b1) (SBody b3))
                 (SSeq (SBody b2) (SBody b3)))) 0.
Proof.
  intros b0 b1 b2 b3 c.
  set (g := diamond b0 b1 b2 b3 c).
  assert (H3 : Realizes g (SBody b3) 3) by (apply (realize_ret g 3); reflexivity).
  assert (H1 : Realizes g (SSeq (SBody b1) (SBody b3)) 1)
    by (apply (realize_goto g 1 3); [reflexivity | exact H3]).
  assert (H2 : Realizes g (SSeq (SBody b2) (SBody b3)) 2)
    by (apply (realize_goto g 2 3); [reflexivity | exact H3]).
  apply (realize_if g 0 c 1 2); [reflexivity | exact H1 | exact H2].
Qed.

(** Sanity: the CFG semantics is DETERMINISTIC (a block's body/terminator are functions), so
    [Realizes] pins the unique result — there is no ambiguity in "what the CFG computes". *)
Lemma cfg_halts_det : forall g l s sf1 sf2,
  cfg_halts g l s sf1 -> cfg_halts g l s sf2 -> sf1 = sf2.
Proof.
  intros g l s sf1 sf2 H1. revert sf2.
  induction H1 as [l s Ht | l l' s sf Ht Hh IH | l c a b s sf Ht Hh IH]; intros sf2 H2.
  - inversion H2 as [l0 s0 Ht2 E0 E1 | l0 l' s0 sf0 Ht2 Hh2 | l0 c a b s0 sf0 Ht2 Hh2];
      subst; [reflexivity | rewrite Ht in Ht2; discriminate | rewrite Ht in Ht2; discriminate].
  - inversion H2 as [l0 s0 Ht2 | l0 l'2 s0 sf0 Ht2 Hh2 | l0 c a b s0 sf0 Ht2 Hh2];
      subst; [rewrite Ht in Ht2; discriminate | | rewrite Ht in Ht2; discriminate].
    rewrite Ht in Ht2. injection Ht2 as <-. exact (IH _ Hh2).
  - inversion H2 as [l0 s0 Ht2 | l0 l'2 s0 sf0 Ht2 Hh2 | l0 c2 a2 b2 s0 sf0 Ht2 Hh2];
      subst; [rewrite Ht in Ht2; discriminate | rewrite Ht in Ht2; discriminate |].
    rewrite Ht in Ht2. injection Ht2 as <- <- <-. exact (IH _ Hh2).
Qed.

(** ════════════════════════════════════════════════════════════════════════════════════════════════
    CYCLIC CFGs → structured LOOPS — the genuinely hard part of relooping.
    ════════════════════════════════════════════════════════════════════════════════════════════════
    A back-edge (a block that gotos an ancestor) cannot be lowered by the acyclic recipe: the
    duplicating unfolding would not terminate, and a total [Fixpoint] cannot even DENOTE a
    possibly-non-terminating loop.  So the structured target gains [LLoop]/[LBreak], its semantics goes
    RELATIONAL (mirroring [cfg_halts]), and the loop lowering is proved by INDUCTION ON THE [cfg_halts]
    DERIVATION (i.e. on the number of loop iterations).  We verify the canonical WHILE loop. *)

Inductive outcome : Type := Normal | Broke.

(** Structured language WITH loops: [LLoop body] runs [body] repeatedly; a [LBreak] inside exits the
    nearest enclosing loop (the loop then finishes [Normal]). *)
Inductive Stmt2 : Type :=
  | LBody  : (State -> State) -> Stmt2
  | LSeq   : Stmt2 -> Stmt2 -> Stmt2
  | LIf    : (State -> bool) -> Stmt2 -> Stmt2 -> Stmt2
  | LLoop  : Stmt2 -> Stmt2
  | LBreak : Stmt2.

(** Big-step relational semantics with break propagation.  [seval S s s' o]: running [S] from [s]
    yields state [s'] and finishes with outcome [o] ([Normal] = fell off the end, [Broke] = hit a
    break that is still propagating outward).  A loop CONSUMES a break (turns it [Normal]); a
    non-terminating loop simply has no derivation. *)
Inductive seval : Stmt2 -> State -> State -> outcome -> Prop :=
  | se_body  : forall f s, seval (LBody f) s (f s) Normal
  | se_break : forall s, seval LBreak s s Broke
  | se_seq_n : forall a b s s' s'' o,
      seval a s s' Normal -> seval b s' s'' o -> seval (LSeq a b) s s'' o
  | se_seq_b : forall a b s s',
      seval a s s' Broke -> seval (LSeq a b) s s' Broke
  | se_if_t  : forall c a b s s' o, c s = true  -> seval a s s' o -> seval (LIf c a b) s s' o
  | se_if_f  : forall c a b s s' o, c s = false -> seval b s s' o -> seval (LIf c a b) s s' o
  | se_loop_again : forall body s s' s'',
      seval body s s' Normal -> seval (LLoop body) s' s'' Normal -> seval (LLoop body) s s'' Normal
  | se_loop_break : forall body s s',
      seval body s s' Broke -> seval (LLoop body) s s' Normal.

(** Inversion helpers (keep the main proof readable). *)
Lemma seval_body_inv : forall f s s' o, seval (LBody f) s s' o -> s' = f s /\ o = Normal.
Proof. intros f s s' o H; inversion H; subst; split; reflexivity. Qed.

Lemma seval_seq_inv : forall a b s s'' o, seval (LSeq a b) s s'' o ->
  (exists s', seval a s s' Normal /\ seval b s' s'' o) \/ (o = Broke /\ seval a s s'' Broke).
Proof.
  intros a b s s'' o H; inversion H; subst.
  - left; eexists; split; eassumption.
  - right; split; [reflexivity | assumption].
Qed.

(** The canonical WHILE CFG: block 0 = HEADER (run [h], branch on [c] to body/exit); block 1 = BODY
    (run [f], goto header); block 2 (+default) = EXIT (run [e], return).  This is exactly
    [h; while c { f; h }; e] flattened to basic blocks with a back-edge 1→0. *)
Definition whileCFG (h f e : State -> State) (c : State -> bool) : CFG :=
  fun l => match l with
           | 0 => mkBlk h (TIf c 1 2)
           | 1 => mkBlk f (TGoto 0)
           | _ => mkBlk e TRet
           end.

(** Per-block structured realization (the induction motive).  [lb] is the loop body
    [h; if c then f else break]; the header lowers to [loop lb; e], the body to [f; (loop lb; e)]. *)
Definition blockprog (h f e : State -> State) (c : State -> bool) (l : nat) : Stmt2 :=
  let lb := LSeq (LBody h) (LIf c (LBody f) LBreak) in
  match l with
  | 0 => LSeq (LLoop lb) (LBody e)
  | 1 => LSeq (LBody f) (LSeq (LLoop lb) (LBody e))
  | _ => LBody e
  end.

(** THE LOOP LOWERING IS CORRECT: every halting run of the while-CFG from any block is reproduced by
    the structured program for that block.  Proved by induction on the [cfg_halts] derivation — the
    recursive [ch_goto]/[ch_if] at the header is the loop unrolling, and the induction hypothesis is
    exactly "the rest of the loop is already realized". *)
Theorem while_realized : forall h f e c l s sf,
  cfg_halts (whileCFG h f e c) l s sf -> seval (blockprog h f e c l) s sf Normal.
Proof.
  intros h f e c l s sf H.
  induction H as [l s Ht | l l' s sf Ht Hh IH | l c0 a b s sf Ht Hh IH].
  - (* ch_ret: only EXIT blocks (l ∉ {0,1}) return; they lower to [LBody e] *)
    destruct l as [|[|l]]; cbn in Ht |- *; try discriminate. apply se_body.
  - (* ch_goto: only the BODY (l=1) gotos — to the header (l'=0) *)
    destruct l as [|[|l]]; cbn in Ht |- *; try discriminate.
    injection Ht as Hl'; subst l'. cbn in IH |- *.
    eapply se_seq_n; [apply se_body | exact IH].
  - (* ch_if: only the HEADER (l=0) branches — c picks BODY (loop again) or EXIT (break) *)
    destruct l as [|[|l]]; cbn in Ht |- *; try discriminate.
    injection Ht as Hc Ha Hb; subst c0 a b.
    cbn in Hh, IH |- *. destruct (c (h s)) eqn:E.
    + (* c true: one more iteration, then the loop continues (from IH at the header) *)
      cbn in IH. apply seval_seq_inv in IH. destruct IH as [[smid [Hf Hrest]] | [Hbad _]];
        [| discriminate].
      apply seval_body_inv in Hf. destruct Hf as [-> _].
      apply seval_seq_inv in Hrest. destruct Hrest as [[s2 [Hloop He]] | [Hbad _]];
        [| discriminate].
      eapply se_seq_n; [| exact He].
      eapply se_loop_again; [| exact Hloop].
      eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact E | apply se_body].
    + (* c false: the loop breaks this iteration, then runs the exit [e] *)
      cbn in IH. apply seval_body_inv in IH. destruct IH as [-> _].
      eapply se_seq_n; [| apply se_body ].
      apply se_loop_break.
      eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact E | apply se_break].
Qed.

End Relooper.
