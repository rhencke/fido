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

    SCOPE (honest): ACYCLIC CFGs lowered to nested if/seq, with the join block DUPLICATED into both
    branches (semantically correct; the plugin's no-duplication relooping is an optimisation atop this
    correctness core).  CYCLIC CFGs → structured LOOPS (break/continue) are the genuinely hard frontier
    and are NOT yet here — see the note at the end.  Proof-only: emits no Go. *)

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

End Relooper.

(** ── The HARD FRONTIER (not yet done): CYCLIC CFGs → structured LOOPS. ──
    A back-edge (a block that gotos an ancestor) cannot be lowered by the acyclic recipe — the
    duplicating unfolding would not terminate, and [srun] (a total [Fixpoint]) cannot even DENOTE a
    possibly-non-terminating loop.  The structured target must gain [SLoop]/[SBreak], its semantics
    must go RELATIONAL/partial (mirroring [cfg_halts]), and the loop combinator must be proved by
    INDUCTION ON THE NUMBER OF ITERATIONS (the [cfg_halts] derivation height).  That is the genuine
    research step — the part of relooping that is actually hard — and is the next target. *)
