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

    SCOPE (honest):
    (1) ACYCLIC, duplicating: the [Realizes] combinators + [diamond_realized] (join duplicated into
        both branches — the simplest correct lowering).
    (2) CYCLIC → LOOPS (the genuinely hard part): a relational [seval] with [LLoop]/[LBreak], and
        [while_realized] — the canonical while-loop CFG (back-edge) lowered to [loop { … break }],
        proved by INDUCTION ON THE [cfg_halts] DERIVATION (the loop-iteration count).
    (3) ACYCLIC, GENERAL + NO-duplication: a run-to-a-LABEL semantics [runs_to] and the key
        [runs_to_halts] (region-reaches-join ∘ join-reaches-HALT, UNCONDITIONAL — the trick that
        dodges the join-revisit hazard), giving compositional combinators [realize_seq]/
        [realizeTo_goto]/[realizeTo_if] and [diamond_general] — the diamond re-lowered with the join
        emitted ONCE.  These are the per-step SOUNDNESS for an arbitrary acyclic relooper.
    (4) The acyclic relooper as an ALGORITHM: [reloop fuel g l] (fuel-bounded, so total without a
        well-founded order — returns [None] on a cycle/out-of-fuel, [Some S] otherwise) with SOUNDNESS
        [reloop_correct] (every [Some S] realizes the CFG), exercised end-to-end by
        [diamond_reloop_correct] (the function COMPUTES the diamond's lowering, certified correct), and
        COMPLETENESS [reloop_complete]/[reloop_total_correct] — a [Ranked g rank] witness (a measure
        dropping along every edge = acyclicity) gives fuel [rank l + 1] that SUCCEEDS, so on any
        acyclic CFG [reloop] is TOTAL ∧ SOUND ∧ COMPLETE ([diamond_reloops] instantiates it).
    All axiom-free.  STILL OPEN: folding LOOPS into the function (it currently refuses back-edges — the
    loop CORE is proved separately, [while_realized]), and connecting to the actual emitted Go AST.
    Proof-only: emits no Go. *)

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

(** ── The acyclic relooper as an actual ALGORITHM (not just combinators). ──
    [reloop fuel g l] runs the acyclic recipe from block [l]: a [TRet] becomes its body, a [TGoto]
    sequences before the target's lowering, a [TIf] sequences before an [SIf] over the two branches
    (the join is DUPLICATED — each branch recurses independently).  [fuel] bounds the recursion, so the
    function is TOTAL (structural on [fuel]) without a well-founded-order argument: it returns [None] if
    fuel runs out or a back-edge sends it round a cycle (the acyclic algorithm correctly REFUSES a
    cyclic CFG), and [Some S] otherwise.  [reloop_correct] is SOUNDNESS — whenever it returns [Some S],
    that [S] provably realizes the CFG (so the algorithm is correct by construction, independent of
    fuel/acyclicity).  [reloop] is `option`-valued, so it emits no Go regardless. *)
Fixpoint reloop (fuel : nat) (g : CFG) (l : nat) : option Stmt :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match blk_term (g l) with
      | TRet      => Some (SBody (blk_body (g l)))
      | TGoto l'  => option_map (fun S => SSeq (SBody (blk_body (g l))) S) (reloop fuel' g l')
      | TIf c a b =>
          match reloop fuel' g a, reloop fuel' g b with
          | Some Sa, Some Sb => Some (SSeq (SBody (blk_body (g l))) (SIf c Sa Sb))
          | _, _ => None
          end
      end
  end.

Lemma reloop_correct : forall fuel g l S, reloop fuel g l = Some S -> Realizes g S l.
Proof.
  induction fuel as [|fuel IH]; intros g l S Hr; cbn in Hr; [discriminate |].
  destruct (blk_term (g l)) eqn:Ht.
  - (* TRet *) injection Hr as <-. apply realize_ret; exact Ht.
  - (* TGoto *) destruct (reloop fuel g n) as [S'|] eqn:Hr'; cbn in Hr; [|discriminate].
    injection Hr as <-. apply (realize_goto g l n); [exact Ht | apply IH; exact Hr'].
  - (* TIf *) destruct (reloop fuel g n) as [Sa|] eqn:Hra; [|discriminate].
    destruct (reloop fuel g n0) as [Sb|] eqn:Hrb; [|discriminate].
    injection Hr as <-. apply (realize_if g l b n n0); [exact Ht | apply IH; exact Hra | apply IH; exact Hrb].
Qed.

(** End-to-end: the FUNCTION computes the diamond's lowering (by [reflexivity] on [reloop 4 …]) and
    [reloop_correct] certifies it — the relooper, run as an algorithm, is correct on a real CFG. *)
Theorem diamond_reloop_correct : forall b0 b1 b2 b3 c,
  Realizes (diamond b0 b1 b2 b3 c)
    (SSeq (SBody b0) (SIf c (SSeq (SBody b1) (SBody b3)) (SSeq (SBody b2) (SBody b3)))) 0.
Proof. intros. apply (reloop_correct 4). reflexivity. Qed.

(** ── COMPLETENESS of [reloop] — acyclic ⇒ it SUCCEEDS (returns [Some]). ──
    This is the piece fuel does NOT dodge: it needs an actual DECREASING MEASURE.  [Ranked g rank]
    says a [rank : nat -> nat] strictly DROPS along every edge (goto target, both if-branches) — which
    IS acyclicity, carried as an explicit witness (no path can cycle, since rank would have to drop
    forever).  Then fuel [rank l + 1] is enough for [reloop] to bottom out at [TRet]s — proved by
    induction on fuel, the rank drop feeding the IH at strictly smaller fuel. *)
Definition Ranked (g : CFG) (rank : nat -> nat) : Prop :=
  forall l, match blk_term (g l) with
            | TRet      => True
            | TGoto l'  => rank l' < rank l
            | TIf _ a b => rank a < rank l /\ rank b < rank l
            end.

Lemma reloop_complete : forall g rank, Ranked g rank ->
  forall fuel l, rank l < fuel -> exists S, reloop fuel g l = Some S.
Proof.
  intros g rank HR. induction fuel as [|fuel IH]; intros l Hlt; [exfalso; lia |].
  cbn. specialize (HR l). destruct (blk_term (g l)) as [| l' | c a b] eqn:Ht.
  - (* TRet *) eexists; reflexivity.
  - (* TGoto: rank l' < rank l < S fuel, so rank l' < fuel *)
    destruct (IH l') as [S' HS']; [lia |]. rewrite HS'. cbn. eexists; reflexivity.
  - (* TIf: both branch ranks < rank l < S fuel *)
    destruct HR as [Ha Hb].
    destruct (IH a) as [Sa HSa]; [lia |]. destruct (IH b) as [Sb HSb]; [lia |].
    rewrite HSa, HSb. eexists; reflexivity.
Qed.

(** The FULL verified acyclic relooper: on any RANKED (acyclic) CFG, [reloop] with fuel [rank l + 1]
    SUCCEEDS and the program it returns REALIZES the CFG.  Total ∧ sound ∧ complete on acyclic inputs. *)
Theorem reloop_total_correct : forall g rank, Ranked g rank ->
  forall l, exists St, reloop (S (rank l)) g l = Some St /\ Realizes g St l.
Proof.
  intros g rank HR l.
  destruct (reloop_complete g rank HR (S (rank l)) l (Nat.lt_succ_diag_r _)) as [St HS].
  exists St. split; [exact HS | exact (reloop_correct _ g l St HS)].
Qed.

(** The diamond is ranked (0↦2, branches 1,2↦1, join 3↦0), so [reloop_total_correct] applies: the
    relooper SUCCEEDS on it and the result is correct — no hand-built fuel constant. *)
Definition diamond_rank : nat -> nat :=
  fun l => match l with 0 => 2 | 1 => 1 | 2 => 1 | _ => 0 end.

Lemma diamond_ranked : forall b0 b1 b2 b3 c, Ranked (diamond b0 b1 b2 b3 c) diamond_rank.
Proof. intros b0 b1 b2 b3 c l. destruct l as [|[|[|l]]]; cbn; lia. Qed.

Theorem diamond_reloops : forall b0 b1 b2 b3 c,
  exists St, reloop (S (diamond_rank 0)) (diamond b0 b1 b2 b3 c) 0 = Some St
             /\ Realizes (diamond b0 b1 b2 b3 c) St 0.
Proof. intros. apply (reloop_total_correct _ diamond_rank), diamond_ranked. Qed.

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

Lemma seval_if_inv : forall c a b s s' o, seval (LIf c a b) s s' o ->
  (c s = true /\ seval a s s' o) \/ (c s = false /\ seval b s s' o).
Proof. intros c a b s s' o H; inversion H; subst; [left|right]; split; assumption. Qed.

Lemma seval_loop_inv : forall body s s' o, seval (LLoop body) s s' o ->
  o = Normal /\ ( (exists smid, seval body s smid Normal /\ seval (LLoop body) smid s' Normal)
                  \/ seval body s s' Broke ).
Proof.
  intros body s s' o H; inversion H; subst; split;
    solve [ reflexivity | left; eexists; split; eassumption | right; assumption ].
Qed.

(** The structured-with-loops TARGET language is DETERMINISTIC: a statement run from a state yields a
    UNIQUE (final state, outcome) whenever it terminates — the loop-language analogue of [cfg_halts_det].
    Without this, "the program the relooper emits" would be ambiguous; with it, [seval] (and hence every
    relooper correctness proof, which pins [seval]) denotes a function.  By induction on the first
    derivation; the loop cases turn on the body's OUTCOME (Normal ⇒ iterate again, Broke ⇒ stop), which
    the IH makes unique, so the two derivations take the same rule. *)
Lemma seval_det : forall S s s1 o1, seval S s s1 o1 ->
  forall s2 o2, seval S s s2 o2 -> s1 = s2 /\ o1 = o2.
Proof.
  intros S s s1 o1 H1.
  induction H1 as
    [ f s | s
    | a b s s' s'' o Ha IHa Hb IHb | a b s s' Ha IHa
    | c a b s s' o Hc Ha IHa | c a b s s' o Hc Hb IHb
    | body s s' s'' Hbody IHbody Hloop IHloop | body s s' Hbody IHbody ];
    intros s2 o2 H2.
  - (* LBody *) inversion H2; subst; split; reflexivity.
  - (* LBreak *) inversion H2; subst; split; reflexivity.
  - (* LSeq, a Normal *) apply seval_seq_inv in H2.
    destruct H2 as [[smid [Ha2 Hb2]] | [_ Hbad]].
    + destruct (IHa _ _ Ha2) as [-> _]. exact (IHb _ _ Hb2).
    + destruct (IHa _ _ Hbad) as [_ Hcon]; discriminate.
  - (* LSeq, a Broke *) apply seval_seq_inv in H2.
    destruct H2 as [[smid [Ha2 _]] | [-> Hbad]].
    + destruct (IHa _ _ Ha2) as [_ Hcon]; discriminate.
    + destruct (IHa _ _ Hbad) as [-> _]; split; reflexivity.
  - (* LIf true *) apply seval_if_inv in H2.
    destruct H2 as [[_ Ha2] | [Hcf _]]; [exact (IHa _ _ Ha2) | rewrite Hc in Hcf; discriminate].
  - (* LIf false *) apply seval_if_inv in H2.
    destruct H2 as [[Hct _] | [_ Hb2]]; [rewrite Hc in Hct; discriminate | exact (IHb _ _ Hb2)].
  - (* LLoop, iterate again (body Normal) *) apply seval_loop_inv in H2.
    destruct H2 as [-> [[smid [Hb2 Hl2]] | Hbrk]].
    + destruct (IHbody _ _ Hb2) as [-> _]. exact (IHloop _ _ Hl2).
    + destruct (IHbody _ _ Hbrk) as [_ Hcon]; discriminate.
  - (* LLoop, break (body Broke) *) apply seval_loop_inv in H2.
    destruct H2 as [-> [[smid [Hb2 _]] | Hbrk]].
    + destruct (IHbody _ _ Hb2) as [_ Hcon]; discriminate.
    + destruct (IHbody _ _ Hbrk) as [-> _]; split; reflexivity.
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

(** ════════════════════════════════════════════════════════════════════════════════════════════════
    GENERAL ACYCLIC relooping — compositional, and WITHOUT join duplication.
    ════════════════════════════════════════════════════════════════════════════════════════════════
    The two hand-built witnesses ([diamond_realized], [while_realized]) point at specific blocks.  To
    relooper an ARBITRARY (acyclic) CFG we need to COMPOSE region lowerings.  The naive composition —
    "region reaches join j₁" then "region reaches join j₂" — is UNSOUND: j₂ may be revisited, so the
    join-to-join transitivity is false without acyclicity.  The fix: always compose
    REGION-REACHES-JOIN with JOIN-REACHES-HALT (terminal) — the second leg cannot be revisited, so the
    composition ([runs_to_halts]) is UNCONDITIONAL.  We peel structured code off the ENTRY toward HALT.

    [runs_to g j l s s']: entering block [l] in state [s], control REACHES the entry of block [j] with
    state [s'] (j's body NOT yet run).  Unlike [cfg_halts] (run to return), this is run-to-a-LABEL. *)
Inductive runs_to (g : CFG) (j : nat) : nat -> State -> State -> Prop :=
  | rt_here : forall s, runs_to g j j s s
  | rt_goto : forall l l' s sf, l <> j -> blk_term (g l) = TGoto l' ->
      runs_to g j l' (blk_body (g l) s) sf -> runs_to g j l s sf
  | rt_if   : forall l c a b s sf, l <> j -> blk_term (g l) = TIf c a b ->
      runs_to g j (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf ->
      runs_to g j l s sf.

(** THE composition: reach [j], then HALT from [j] ⇒ HALT from [l].  Unconditional — the second leg
    is terminal, which is exactly why peeling toward HALT (not join-to-join) avoids the revisit hazard. *)
Lemma runs_to_halts : forall g j l s s1 sf,
  runs_to g j l s s1 -> cfg_halts g j s1 sf -> cfg_halts g l s sf.
Proof.
  intros g j l s s1 sf H. revert sf.
  induction H as [s | l l' s sf Hne Ht Hr IH | l c a b s sf Hne Ht Hr IH]; intros sf2 Hh.
  - exact Hh.
  - eapply ch_goto; [exact Ht | apply IH; exact Hh].
  - eapply ch_if;   [exact Ht | apply IH; exact Hh].
Qed.

(** [RealizesTo g S l j]: structured [S] computes the state at which the CFG, entered at [l], reaches
    join [j].  ([Realizes] from the acyclic section is the [j]=HALT special case, modulo [cfg_halts].) *)
Definition RealizesTo (g : CFG) (S : Stmt) (l j : nat) : Prop :=
  forall s, runs_to g j l s (srun S s).

(** PEEL — region [l→j] then [j→halt] composes to [l→halt], no side condition. *)
Lemma realize_seq : forall g S1 S2 l j,
  RealizesTo g S1 l j -> Realizes g S2 j -> Realizes g (SSeq S1 S2) l.
Proof. intros g S1 S2 l j H1 H2 s. cbn. eapply runs_to_halts; [apply H1 | apply H2]. Qed.

(** A [TGoto l'] block reaches its target ([l ≠ l'], else it is a self-loop and never reaches). *)
Lemma realizeTo_goto : forall g l l',
  l <> l' -> blk_term (g l) = TGoto l' -> RealizesTo g (SBody (blk_body (g l))) l l'.
Proof. intros g l l' Hne Ht s. cbn. eapply rt_goto; [exact Hne | exact Ht | apply rt_here]. Qed.

(** An [TIf] block whose BOTH branches reach a common join [j] (≠ l) — lowered with the join SHARED
    (emitted ONCE, after the [if]), i.e. NO duplication. *)
Lemma realizeTo_if : forall g l c a b j Sa Sb,
  l <> j -> blk_term (g l) = TIf c a b -> RealizesTo g Sa a j -> RealizesTo g Sb b j ->
  RealizesTo g (SSeq (SBody (blk_body (g l))) (SIf c Sa Sb)) l j.
Proof.
  intros g l c a b j Sa Sb Hne Ht HRa HRb s. cbn.
  eapply rt_if; [exact Hne | exact Ht |]. cbn.
  destruct (c (blk_body (g l) s)) eqn:E; [apply HRa | apply HRb].
Qed.

(** PAYOFF: the if-diamond re-lowered through the GENERAL combinators — and with the join [b3] emitted
    ONCE (not duplicated into both branches as [diamond_realized] did):  b0 ; if c {b1} else {b2} ; b3.
    Built compositionally, so the same recipe relooper any acyclic CFG (the remaining piece is the
    recursive relooper FUNCTION + its well-founded termination, not the per-step soundness — that is
    these lemmas). *)
Theorem diamond_general : forall b0 b1 b2 b3 c,
  Realizes (diamond b0 b1 b2 b3 c)
    (SSeq (SSeq (SBody b0) (SIf c (SBody b1) (SBody b2))) (SBody b3)) 0.
Proof.
  intros b0 b1 b2 b3 c. set (g := diamond b0 b1 b2 b3 c).
  assert (H3 : Realizes g (SBody b3) 3) by (apply (realize_ret g 3); reflexivity).
  assert (HR1 : RealizesTo g (SBody b1) 1 3)
    by (apply (realizeTo_goto g 1 3); [discriminate | reflexivity]).
  assert (HR2 : RealizesTo g (SBody b2) 2 3)
    by (apply (realizeTo_goto g 2 3); [discriminate | reflexivity]).
  assert (HR0 : RealizesTo g (SSeq (SBody b0) (SIf c (SBody b1) (SBody b2))) 0 3)
    by (apply (realizeTo_if g 0 c 1 2 3); [discriminate | reflexivity | exact HR1 | exact HR2]).
  apply (realize_seq g _ (SBody b3) 0 3); [exact HR0 | exact H3].
Qed.

End Relooper.
