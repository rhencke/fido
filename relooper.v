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

From Stdlib Require Import List Lia Arith Wf_nat.
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

(** ── LOOP whose BODY BRANCHES — the relooper composing a LOOP with a CONDITIONAL (beyond
    [while_realized]'s straight-line body).  CFG:
      0 header: run [h], branch [c] to BODY(1) / EXIT(4);  1 body: run [f], branch [c2] to A(2)/B(3);
      2 A: run [a], goto header;  3 B: run [b], goto header;  4 exit: run [e], return.
    i.e. [loop { h; if c { f; if c2 then a else b } else break } ; e].  Proved, like [while_realized],
    by induction on the [cfg_halts] derivation, but now the loop body has a nested [if] (c2) AND the
    back-edge is reached from EITHER inner branch — exercising the loop/conditional interaction. *)
Definition loopifCFG (h f a b e : State -> State) (c c2 : State -> bool) : CFG :=
  fun l => match l with
           | 0 => mkBlk h (TIf c 1 4)
           | 1 => mkBlk f (TIf c2 2 3)
           | 2 => mkBlk a (TGoto 0)
           | 3 => mkBlk b (TGoto 0)
           | _ => mkBlk e TRet
           end.

Definition loopif_prog (h f a b e : State -> State) (c c2 : State -> bool) (l : nat) : Stmt2 :=
  let lb := LSeq (LBody h) (LIf c (LSeq (LBody f) (LIf c2 (LBody a) (LBody b))) LBreak) in
  let tail := LSeq (LLoop lb) (LBody e) in
  match l with
  | 0 => tail
  | 1 => LSeq (LSeq (LBody f) (LIf c2 (LBody a) (LBody b))) tail
  | 2 => LSeq (LBody a) tail
  | 3 => LSeq (LBody b) tail
  | _ => LBody e
  end.

Theorem loopif_realized : forall h f a b e c c2 l s sf,
  cfg_halts (loopifCFG h f a b e c c2) l s sf -> seval (loopif_prog h f a b e c c2 l) s sf Normal.
Proof.
  intros h f a b e c c2 l s sf H.
  induction H as [l s Ht | l l' s sf Ht Hh IH | l c0 a0 b0 s sf Ht Hh IH].
  - (* ch_ret: only the EXIT (l ≥ 4) returns → [LBody e] *)
    destruct l as [|[|[|[|l]]]]; cbn in Ht |- *; try discriminate. apply se_body.
  - (* ch_goto: only A(2)/B(3) goto the header(0) *)
    destruct l as [|[|[|[|l]]]]; cbn in Ht |- *; try discriminate;
      injection Ht as Hl'; subst l'; cbn in IH |- *; eapply se_seq_n; first [apply se_body | exact IH].
  - (* ch_if: the HEADER(0) branches on c; the BODY(1) branches on c2 *)
    destruct l as [|[|[|[|l]]]]; cbn in Ht |- *; try discriminate.
    + (* HEADER: c picks BODY (loop again) or EXIT (break) *)
      injection Ht as Hc Ha Hb; subst c0 a0 b0. cbn in Hh, IH |- *. destruct (c (h s)) eqn:E.
      * (* c true: run one iteration's body (f; if c2 {a} else {b}), then the loop continues *)
        apply seval_seq_inv in IH. destruct IH as [[smid [Hbody Hrest]] | [Hbad _]]; [| discriminate].
        apply seval_seq_inv in Hrest. destruct Hrest as [[s2 [Hloop He]] | [Hbad _]]; [| discriminate].
        eapply se_seq_n; [| exact He]. eapply se_loop_again; [| exact Hloop].
        eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact E | exact Hbody].
      * (* c false: the loop breaks, then exit [e] *)
        apply seval_body_inv in IH. destruct IH as [-> _].
        eapply se_seq_n; [| apply se_body]. apply se_loop_break.
        eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact E | apply se_break].
    + (* BODY: c2 picks A or B; either way run it then continue the loop *)
      injection Ht as Hc2 Ha Hb; subst c0 a0 b0. cbn in Hh, IH |- *. destruct (c2 (f s)) eqn:E2.
      * (* c2 true: A *)
        apply seval_seq_inv in IH. destruct IH as [[smid [Ha2 Hrest]] | [Hbad _]]; [| discriminate].
        apply seval_body_inv in Ha2. destruct Ha2 as [-> _].
        eapply se_seq_n; [| exact Hrest].
        eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact E2 | apply se_body].
      * (* c2 false: B *)
        apply seval_seq_inv in IH. destruct IH as [[smid [Hb2 Hrest]] | [Hbad _]]; [| discriminate].
        apply seval_body_inv in Hb2. destruct Hb2 as [-> _].
        eapply se_seq_n; [| exact Hrest].
        eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact E2 | apply se_body].
Qed.

(** ── NESTED LOOPS — an OUTER loop containing an INNER loop, exercising [LBreak]'s "nearest enclosing
    loop" scoping.  CFG:
      0 OUTER-header: run [h1], branch [c1] to INNER-header(1) / OUTER-exit(3);
      1 INNER-header: run [h2], branch [c2] to INNER-body(2) / back to OUTER-header(0);
      2 INNER-body:   run [f], goto INNER-header(1);   3 OUTER-exit: run [e], return.
    So [c2]-false EXITS the inner loop (its break) which falls through to the OUTER loop's iteration
    (back to 0), and [c1]-false breaks the OUTER loop:
      loop { h1; if c1 { loop { h2; if c2 then f else break } } else break } ; e.
    The inner [break] must exit ONLY the inner loop — the proof's [se_loop_break] on the inner [LLoop]
    leaves the outer [LLoop] to continue, exactly the nearest-enclosing semantics.  Proved by induction
    on the [cfg_halts] derivation, peeling the (now doubly-nested) loop continuations with the [seval]
    inversion helpers. *)
Definition nestloopCFG (h1 h2 f e : State -> State) (c1 c2 : State -> bool) : CFG :=
  fun l => match l with
           | 0 => mkBlk h1 (TIf c1 1 3)
           | 1 => mkBlk h2 (TIf c2 2 0)
           | 2 => mkBlk f (TGoto 1)
           | _ => mkBlk e TRet
           end.

Definition nestloop_prog (h1 h2 f e : State -> State) (c1 c2 : State -> bool) (l : nat) : Stmt2 :=
  let inner_lb := LSeq (LBody h2) (LIf c2 (LBody f) LBreak) in
  let outer_lb := LSeq (LBody h1) (LIf c1 (LLoop inner_lb) LBreak) in
  let otail := LSeq (LLoop outer_lb) (LBody e) in
  match l with
  | 0 => otail
  | 1 => LSeq (LLoop inner_lb) otail
  | 2 => LSeq (LBody f) (LSeq (LLoop inner_lb) otail)
  | _ => LBody e
  end.

Theorem nestloop_realized : forall h1 h2 f e c1 c2 l s sf,
  cfg_halts (nestloopCFG h1 h2 f e c1 c2) l s sf -> seval (nestloop_prog h1 h2 f e c1 c2 l) s sf Normal.
Proof.
  intros h1 h2 f e c1 c2 l s sf H.
  induction H as [l s Ht | l l' s sf Ht Hh IH | l c0 a0 b0 s sf Ht Hh IH].
  - (* ch_ret: only OUTER-exit (l ≥ 3) returns *)
    destruct l as [|[|[|l]]]; cbn in Ht |- *; try discriminate. apply se_body.
  - (* ch_goto: only INNER-body(2) gotos INNER-header(1) *)
    destruct l as [|[|[|l]]]; cbn in Ht |- *; try discriminate.
    injection Ht as Hl'; subst l'. cbn in IH |- *. eapply se_seq_n; [apply se_body | exact IH].
  - (* ch_if: OUTER-header(0) on c1, INNER-header(1) on c2 *)
    destruct l as [|[|[|l]]]; cbn in Ht |- *; try discriminate.
    + (* OUTER-header: c1 picks the inner loop (then outer continues) or breaks the outer loop *)
      injection Ht as Hc Ha Hb; subst c0 a0 b0. cbn in Hh, IH |- *. destruct (c1 (h1 s)) eqn:E.
      * (* c1 true: run the WHOLE inner loop, then the outer loop iterates *)
        apply seval_seq_inv in IH. destruct IH as [[s' [Hinner Hrest]] | [Hbad _]]; [| discriminate].
        apply seval_seq_inv in Hrest. destruct Hrest as [[s2 [Houter He]] | [Hbad _]]; [| discriminate].
        eapply se_seq_n; [| exact He]. eapply se_loop_again; [| exact Houter].
        eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact E | exact Hinner].
      * (* c1 false: break the outer loop, then exit *)
        apply seval_body_inv in IH. destruct IH as [-> _].
        eapply se_seq_n; [| apply se_body]. apply se_loop_break.
        eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact E | apply se_break].
    + (* INNER-header: c2 picks the inner body (inner loop iterates) or breaks the INNER loop (outer continues) *)
      injection Ht as Hc Ha Hb; subst c0 a0 b0. cbn in Hh, IH |- *. destruct (c2 (h2 s)) eqn:E2.
      * (* c2 true: one inner iteration (run f), then the inner loop continues *)
        apply seval_seq_inv in IH. destruct IH as [[smid [Hf Hrest]] | [Hbad _]]; [| discriminate].
        apply seval_body_inv in Hf. destruct Hf as [-> _].
        apply seval_seq_inv in Hrest. destruct Hrest as [[s2 [Hinner Houter]] | [Hbad _]]; [| discriminate].
        eapply se_seq_n; [| exact Houter]. eapply se_loop_again; [| exact Hinner].
        eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact E2 | apply se_body].
      * (* c2 false: BREAK THE INNER LOOP (nearest enclosing) — the OUTER loop then continues *)
        eapply se_seq_n; [| exact IH]. apply se_loop_break.
        eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact E2 | apply se_break].
Qed.

(** ── The LOOP-AWARE relooper as a FUNCTION (the acyclic [reloop] refused back-edges) — gap #10's #1
    open item, FIRST SLICE.  Given a SINGLE loop with header [hdr] and exit block [exit], [reloop_loop]
    emits [LLoop body ; after] where [reloop_b] relooper the loop BODY treating a back-edge to [hdr] as
    FALL-THROUGH (the [LLoop] then iterates) and the [exit] block as [LBreak], and [after] is the acyclic
    relooping of the exit (lifted into the loop language).  This is the loop analogue of
    [diamond_reloop_correct]: the FUNCTION computes the canonical while-loop's lowering, certified correct
    here on [whileCFG] via [while_realized].  (GENERAL soundness — [reloop_loop] correct for ANY
    single-loop CFG — generalises [while_realized] to the algorithm's output; the next slice.  Multi-level
    loops need labelled break, which [seval]'s nearest-only [LBreak] lacks — so single-loop is the clean
    scope.) *)
Fixpoint lift (S : Stmt) : Stmt2 :=
  match S with
  | SBody f   => LBody f
  | SSeq a b  => LSeq (lift a) (lift b)
  | SIf c a b => LIf c (lift a) (lift b)
  end.

Fixpoint reloop_b (hdr exit : nat) (fuel : nat) (g : CFG) (l : nat) : option Stmt2 :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Nat.eqb l exit then Some LBreak
      else match blk_term (g l) with
           | TRet => None   (* a return INSIDE the loop body: [seval] has no return, refuse (honest) *)
           | TGoto l' =>
               if Nat.eqb l' hdr
               then Some (LBody (blk_body (g l)))   (* back-edge to header: run body, then the LLoop iterates *)
               else option_map (fun S => LSeq (LBody (blk_body (g l))) S) (reloop_b hdr exit fuel' g l')
           | TIf c a b =>
               match reloop_b hdr exit fuel' g a, reloop_b hdr exit fuel' g b with
               | Some Sa, Some Sb => Some (LSeq (LBody (blk_body (g l))) (LIf c Sa Sb))
               | _, _ => None
               end
           end
  end.

Definition reloop_loop (hdr exit : nat) (fuel : nat) (g : CFG) : option Stmt2 :=
  match reloop_b hdr exit fuel g hdr, reloop fuel g exit with
  | Some body, Some aft => Some (LSeq (LLoop body) (lift aft))
  | _, _ => None
  end.

(** The FUNCTION computes [whileCFG]'s loop lowering (by computation) — exactly [blockprog … 0]. *)
Theorem whileCFG_reloop_loop : forall h f e c,
  reloop_loop 0 2 5 (whileCFG h f e c) = Some (blockprog h f e c 0).
Proof. intros. reflexivity. Qed.

(** …and that lowering is CORRECT: every halting run of the while-CFG is reproduced by the structured
    program the FUNCTION emits — the loop analogue of [diamond_reloop_correct]. *)
Theorem whileCFG_reloop_loop_correct : forall h f e c s sf,
  cfg_halts (whileCFG h f e c) 0 s sf ->
  exists S, reloop_loop 0 2 5 (whileCFG h f e c) = Some S /\ seval S s sf Normal.
Proof.
  intros h f e c s sf H. exists (blockprog h f e c 0).
  split; [apply whileCFG_reloop_loop | exact (while_realized h f e c 0 s sf H)].
Qed.

(** Toward GENERAL [reloop_loop] soundness — the EMBEDDING is faithful: the loop-language [seval] of a
    [lift]ed acyclic statement reproduces its total [srun] semantics (and finishes [Normal] — an [SIf]/
    [SSeq]/[SBody] never breaks).  This is the bridge the loop-aware relooper needs for its AFTER-loop
    code, which is the acyclic [reloop] lifted into the loop language. *)
Lemma lift_correct : forall S s, seval (lift S) s (srun S s) Normal.
Proof.
  induction S as [f | a IHa b IHb | c a IHa b IHb]; intros s; cbn.
  - apply se_body.
  - eapply se_seq_n; [apply IHa | apply IHb].
  - destruct (c s) eqn:E; [eapply se_if_t | eapply se_if_f]; solve [exact E | apply IHa | apply IHb].
Qed.

(** Hence the AFTER-LOOP half of [reloop_loop] is sound: when the acyclic relooper handles the exit
    region ([reloop … exit = Some aft]), its [lift]ed form, run from the exit's entry state, BOTH matches
    the [seval] semantics AND reproduces the CFG's run from the exit ([reloop_correct]).  (The remaining
    half — the [LLoop body] iterations realizing the loop — generalises [while_realized] to [reloop_b]'s
    output; the next slice.) *)
Lemma reloop_after_realizes : forall fuel g exit aft s,
  reloop fuel g exit = Some aft ->
  seval (lift aft) s (srun aft s) Normal /\ cfg_halts g exit s (srun aft s).
Proof.
  intros fuel g exit aft s Hr. split.
  - apply lift_correct.
  - exact (reloop_correct fuel g exit aft Hr s).
Qed.

(** ── The LOOP-BODY half of general [reloop_loop] soundness — the genuinely hard part. ──
    [runs_term g hdr exit l s s' o]: ONE pass of the loop body, entered at block [l], runs the CFG until
    it either reaches the [exit] block ([o = Broke], a break) or follows a back-edge to [hdr] ([o = Normal],
    iterate) — the operational meaning of "one loop iteration".  [reloop_b_correct] is the analogue of the
    acyclic [reloop_correct]: whenever [reloop_b] returns [Some S], that [S] REALIZES [runs_term] — its
    [seval] reproduces exactly the one-iteration outcome and state.  This is the body-region soundness the
    full [LLoop] composition (the next slice) builds on, the loop counterpart of [reloop_correct]. *)
Inductive runs_term (g : CFG) (hdr exit : nat) : nat -> State -> State -> outcome -> Prop :=
  | rterm_exit : forall s, runs_term g hdr exit exit s s Broke
  | rterm_back : forall l s, l <> exit -> blk_term (g l) = TGoto hdr ->
       runs_term g hdr exit l s (blk_body (g l) s) Normal
  | rterm_goto : forall l l' s s' o, l <> exit -> blk_term (g l) = TGoto l' -> l' <> hdr ->
       runs_term g hdr exit l' (blk_body (g l) s) s' o -> runs_term g hdr exit l s s' o
  | rterm_if : forall l c a b s s' o, l <> exit -> blk_term (g l) = TIf c a b ->
       runs_term g hdr exit (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) s' o ->
       runs_term g hdr exit l s s' o.

Lemma reloop_b_correct : forall hdr exit fuel g l S,
  reloop_b hdr exit fuel g l = Some S ->
  forall s, exists s' o, runs_term g hdr exit l s s' o /\ seval S s s' o.
Proof.
  intros hdr exit. induction fuel as [|fuel IH]; intros g l S Hr s; cbn in Hr; [discriminate|].
  destruct (Nat.eqb l exit) eqn:Eex.
  - apply Nat.eqb_eq in Eex; subst l. injection Hr as <-.
    exists s, Broke. split; [apply rterm_exit | apply se_break].
  - apply Nat.eqb_neq in Eex. destruct (blk_term (g l)) as [ | n | cnd a1 a2] eqn:Ht.
    + discriminate Hr.
    + destruct (Nat.eqb n hdr) eqn:Eh.
      * apply Nat.eqb_eq in Eh; subst n. injection Hr as <-.
        exists (blk_body (g l) s), Normal. split; [apply rterm_back; assumption | apply se_body].
      * apply Nat.eqb_neq in Eh.
        destruct (reloop_b hdr exit fuel g n) as [S'|] eqn:Hr'; cbn in Hr; [|discriminate].
        injection Hr as <-.
        destruct (IH g n S' Hr' (blk_body (g l) s)) as [s' [o [Hrt Hsev]]].
        exists s', o. split.
        -- eapply rterm_goto; [exact Eex | exact Ht | exact Eh | exact Hrt].
        -- eapply se_seq_n; [apply se_body | exact Hsev].
    + destruct (reloop_b hdr exit fuel g a1) as [Sa|] eqn:Hra; [|discriminate].
      destruct (reloop_b hdr exit fuel g a2) as [Sb|] eqn:Hrb; [|discriminate].
      injection Hr as <-. destruct (cnd (blk_body (g l) s)) eqn:Ec.
      * destruct (IH g a1 Sa Hra (blk_body (g l) s)) as [s' [o [Hrt Hsev]]].
        exists s', o. split.
        -- eapply rterm_if; [exact Eex | exact Ht |]. rewrite Ec. exact Hrt.
        -- eapply se_seq_n; [apply se_body |]. eapply se_if_t; [exact Ec | exact Hsev].
      * destruct (IH g a2 Sb Hrb (blk_body (g l) s)) as [s' [o [Hrt Hsev]]].
        exists s', o. split.
        -- eapply rterm_if; [exact Eex | exact Ht |]. rewrite Ec. exact Hrt.
        -- eapply se_seq_n; [apply se_body |]. eapply se_if_f; [exact Ec | apply Hsev].
Qed.

(** [runs_term] FACTORS [cfg_halts]: the CFG is deterministic, so ONE loop iteration (a [runs_term] from
    [l] to a terminal) is a prefix of the whole halting run from [l] — the run then CONTINUES from the
    terminal ([hdr] on Normal/iterate, [exit] on Broke/break).  This bridges the loop-body soundness
    ([reloop_b_correct], stated over [runs_term]) to the CFG's [cfg_halts], the ingredient the final
    [LLoop] composition needs (the composition itself = a well-founded induction over the iterations). *)
Lemma cfg_halts_goto_inv : forall g l l' s sf,
  blk_term (g l) = TGoto l' -> cfg_halts g l s sf -> cfg_halts g l' (blk_body (g l) s) sf.
Proof.
  intros g l l' s sf Ht H.
  inversion H as [l0 s0 Hr | l0 l'0 s0 sf0 Hg Hh | l0 c0 a0 b0 s0 sf0 Hi Hh]; subst.
  - rewrite Ht in Hr; discriminate.
  - rewrite Ht in Hg; injection Hg as <-; exact Hh.
  - rewrite Ht in Hi; discriminate.
Qed.

Lemma cfg_halts_if_inv : forall g l c a b s sf,
  blk_term (g l) = TIf c a b -> cfg_halts g l s sf ->
  cfg_halts g (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf.
Proof.
  intros g l c a b s sf Ht H.
  inversion H as [l0 s0 Hr | l0 l'0 s0 sf0 Hg Hh | l0 c0 a0 b0 s0 sf0 Hi Hh]; subst.
  - rewrite Ht in Hr; discriminate.
  - rewrite Ht in Hg; discriminate.
  - rewrite Ht in Hi; injection Hi as <- <- <-; exact Hh.
Qed.

Lemma runs_term_cfg : forall g hdr exit l s s' o sf,
  runs_term g hdr exit l s s' o ->
  cfg_halts g l s sf ->
  cfg_halts g (match o with Normal => hdr | Broke => exit end) s' sf.
Proof.
  intros g hdr exit l s s' o sf Hrt. revert sf.
  induction Hrt as [ s | l s Hne Ht | l l' s s' o Hne Ht Hnh Hrt' IH
                   | l c a b s s' o Hne Ht Hrt' IH ]; intros sf Hch.
  - exact Hch.
  - exact (cfg_halts_goto_inv g l hdr s sf Ht Hch).
  - exact (IH sf (cfg_halts_goto_inv g l l' s sf Ht Hch)).
  - exact (IH sf (cfg_halts_if_inv g l c a b s sf Ht Hch)).
Qed.

(** ── The DECREASING MEASURE for the final [LLoop] composition. ──
    The composition chains the loop iterations, but the next-iteration run ([cfg_halts g hdr s']) is a
    NESTED subderivation, not an immediate one — so plain induction gives no IH for it.  The fix: a
    FUEL-INDEXED [cfg_halts_n] (the fuel bounds the derivation depth) as an explicit well-founded measure.
    Each block stepped consumes one fuel ([chn_*]); since one loop iteration steps the header (≥1 block),
    the next iteration runs at STRICTLY smaller fuel — the decrease the strong induction needs. *)
Inductive cfg_halts_n (g : CFG) : nat -> nat -> State -> State -> Prop :=
  | chn_ret  : forall n l s, blk_term (g l) = TRet -> cfg_halts_n g (S n) l s (blk_body (g l) s)
  | chn_goto : forall n l l' s sf, blk_term (g l) = TGoto l' ->
       cfg_halts_n g n l' (blk_body (g l) s) sf -> cfg_halts_n g (S n) l s sf
  | chn_if   : forall n l c a b s sf, blk_term (g l) = TIf c a b ->
       cfg_halts_n g n (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf ->
       cfg_halts_n g (S n) l s sf.

Lemma cfg_halts_to_n : forall g l s sf, cfg_halts g l s sf -> exists n, cfg_halts_n g n l s sf.
Proof.
  intros g l s sf H. induction H.
  - exists 1. apply chn_ret; assumption.
  - destruct IHcfg_halts as [n Hn]. exists (S n). eapply chn_goto; eassumption.
  - destruct IHcfg_halts as [n Hn]. exists (S n). eapply chn_if; eassumption.
Qed.

Lemma cfg_halts_n_to : forall g n l s sf, cfg_halts_n g n l s sf -> cfg_halts g l s sf.
Proof.
  intros g n l s sf H. induction H.
  - apply ch_ret; assumption.
  - eapply ch_goto; eassumption.
  - eapply ch_if; eassumption.
Qed.

(** Peel one fuel-step off a [cfg_halts_n] run — the fuel drops by exactly one per block. *)
Lemma chn_goto_inv : forall g n l l' s sf, blk_term (g l) = TGoto l' ->
  cfg_halts_n g n l s sf -> exists m, n = S m /\ cfg_halts_n g m l' (blk_body (g l) s) sf.
Proof.
  intros g n l l' s sf Ht H.
  inversion H as [m l0 s0 Hr | m l0 l'0 s0 sf0 Hg Hh | m l0 c0 a0 b0 s0 sf0 Hi Hh]; subst.
  - rewrite Ht in Hr; discriminate.
  - rewrite Ht in Hg; injection Hg as <-. exists m. split; [reflexivity | exact Hh].
  - rewrite Ht in Hi; discriminate.
Qed.

Lemma chn_if_inv : forall g n l c a b s sf, blk_term (g l) = TIf c a b ->
  cfg_halts_n g n l s sf ->
  exists m, n = S m /\ cfg_halts_n g m (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf.
Proof.
  intros g n l c a b s sf Ht H.
  inversion H as [m l0 s0 Hr | m l0 l'0 s0 sf0 Hg Hh | m l0 c0 a0 b0 s0 sf0 Hi Hh]; subst.
  - rewrite Ht in Hr; discriminate.
  - rewrite Ht in Hg; discriminate.
  - rewrite Ht in Hi; injection Hi as <- <- <-. exists m. split; [reflexivity | exact Hh].
Qed.

(** [runs_term] FACTORS the FUEL-INDEXED [cfg_halts_n], tracking the fuel.  One loop iteration (a
    [runs_term] from [l] to a terminal) is a PREFIX of the whole [cfg_halts_n] run from [l]; the residual
    run from the terminal ([hdr] on iterate, [exit] on break) uses [n'] fuel with [n' <= n].  And it
    uses STRICTLY LESS ([n' < n]) whenever [l <> exit] — because then the FIRST block ([g l], a [TGoto]/
    [TIf]) is stepped, consuming one fuel before the residual.  This conditional strictness is exactly the
    decreasing measure the [LLoop] composition needs: a real iteration enters at [hdr <> exit], so the next
    iteration runs at strictly smaller fuel.  One induction carries both bounds (the strictness as a
    [l <> exit ->] guarded conjunct, vacuous in the [rterm_exit] base). *)
Lemma runs_term_cfg_n : forall g hdr exit l s s' o n sf,
  runs_term g hdr exit l s s' o ->
  cfg_halts_n g n l s sf ->
  exists n', n' <= n
          /\ cfg_halts_n g n' (match o with Normal => hdr | Broke => exit end) s' sf
          /\ (l <> exit -> n' < n).
Proof.
  intros g hdr exit l s s' o n sf Hrt. revert n sf.
  induction Hrt as [ s | l s Hne Ht | l l' s s' o Hne Ht Hnh Hrt' IH
                   | l c a b s s' o Hne Ht Hrt' IH ]; intros n sf Hch.
  - (* rterm_exit: l = exit, o = Broke, s' = s, target = exit; strictness vacuous *)
    exists n. split; [lia | split; [exact Hch | intros C; exfalso; apply C; reflexivity]].
  - (* rterm_back: TGoto hdr, o = Normal, target = hdr — peel one fuel-step *)
    destruct (chn_goto_inv g n l hdr s sf Ht Hch) as [m [Hn Hm]].
    exists m. subst n. split; [lia | split; [exact Hm | intros _; lia]].
  - (* rterm_goto: TGoto l', recurse from l' on m < n fuel *)
    destruct (chn_goto_inv g n l l' s sf Ht Hch) as [m [Hn Hm]].
    destruct (IH m sf Hm) as [n' [Hle [Hcf _]]].
    exists n'. subst n. split; [lia | split; [exact Hcf | intros _; lia]].
  - (* rterm_if: TIf, recurse on the taken branch on m < n fuel *)
    destruct (chn_if_inv g n l c a b s sf Ht Hch) as [m [Hn Hm]].
    destruct (IH m sf Hm) as [n' [Hle [Hcf _]]].
    exists n'. subst n. split; [lia | split; [exact Hcf | intros _; lia]].
Qed.

(** ── The general [LLoop] composition: the loop body iterates correctly. ──
    [Iterates g hdr exit body] is the abstraction barrier that DECOUPLES the loop machinery from any
    particular body relooper: [body] realises ONE loop iteration from the header — run from any state it
    reproduces the CFG's [runs_term] outcome (back-edge to [hdr] ⇒ [Normal]/iterate, reach [exit] ⇒
    [Broke]/break).  [reloop_b]'s output is one such (just [reloop_b_correct] at [l := hdr]) — but so is a
    [LSeq … (LLoop inner) …] body containing a NESTED inner loop, which is exactly why this abstraction is
    the door to nested-loop bodies (the loop lemma no longer hardcodes the ACYCLIC [reloop_b]). *)
Definition Iterates (g : CFG) (hdr exit : nat) (body : Stmt2) : Prop :=
  forall s, exists s' o, runs_term g hdr exit hdr s s' o /\ seval body s s' o.

(** Whenever [body] realises one iteration ([Iterates]) and the CFG halts from the header in [n] fuel,
    [LLoop body] reproduces the loop: it runs the body once per CFG iteration and STOPS exactly when control
    reaches [exit], leaving the loop in the SAME state [sx] the CFG is in at [exit] — from which [nx] fuel
    remains to finish.  Proof by STRONG induction on the fuel [n] ([lt_wf_ind]): one iteration via the
    [Iterates] hypothesis gives [seval body] + a [runs_term]; [runs_term_cfg_n] factors it out of
    [cfg_halts_n], yielding the residual at strictly smaller fuel (Normal: the header is re-entered with
    [hdr <> exit], so [n' < n] — the IH applies, [se_loop_again]; Broke: [se_loop_break] consumes the break
    and we hand off the residual exit-run). *)
Lemma loop_body_iterates_gen : forall g hdr exit body,
  Iterates g hdr exit body ->
  forall sf n s, cfg_halts_n g n hdr s sf ->
  exists sx nx, seval (LLoop body) s sx Normal /\ cfg_halts_n g nx exit sx sf.
Proof.
  intros g hdr exit body Hit sf n.
  induction n as [n IH] using lt_wf_ind. intros s Hch.
  destruct (Hit s) as [s1 [o [Hrt Hsev]]].
  destruct (runs_term_cfg_n g hdr exit hdr s s1 o n sf Hrt Hch) as [n' [Hle [Hcf Hstrict]]].
  destruct o.
  - (* Normal: a real iteration, so hdr <> exit; recurse at strictly smaller fuel *)
    assert (Hne : hdr <> exit) by (intro Heq; rewrite Heq in Hrt; inversion Hrt; congruence).
    destruct (IH n' (Hstrict Hne) s1 Hcf) as [sx [nx [Hloop Hexit]]].
    exists sx, nx. split; [eapply se_loop_again; [exact Hsev | exact Hloop] | exact Hexit].
  - (* Broke: the loop breaks here, landing at exit in state s1 = sx *)
    exists s1, n'. split; [apply se_loop_break; exact Hsev | exact Hcf].
Qed.

(** [reloop_b]'s output IS an iteration realiser — its correctness ([reloop_b_correct]) at [l := hdr] is
    literally [Iterates]. *)
Lemma reloop_b_iterates : forall hdr exit fuel g body,
  reloop_b hdr exit fuel g hdr = Some body -> Iterates g hdr exit body.
Proof. intros hdr exit fuel g body Hb s. exact (reloop_b_correct hdr exit fuel g hdr body Hb s). Qed.

(** The original [loop_body_iterates] is now the [reloop_b] INSTANCE of the general lemma — same statement,
    so every downstream caller ([reloop_loop_sound], [reloop_chain_sound]) is untouched. *)
Lemma loop_body_iterates : forall hdr exit fuel g body sf n s,
  reloop_b hdr exit fuel g hdr = Some body ->
  cfg_halts_n g n hdr s sf ->
  exists sx nx, seval (LLoop body) s sx Normal /\ cfg_halts_n g nx exit sx sf.
Proof.
  intros hdr exit fuel g body sf n s Hb Hch.
  exact (loop_body_iterates_gen g hdr exit body
           (reloop_b_iterates hdr exit fuel g body Hb) sf n s Hch).
Qed.

(** ── The FULLY ABSTRACT single-loop soundness. ──
    [AfterRealizes g exit A]: the structured tail [A] reproduces the CFG's run from [exit] (run [A] from any
    [exit]-state and it lands wherever the CFG does).  Then [LSeq (LLoop body) A] is sound for ANY iteration-
    realising [body] and ANY exit-realising [A] — the loop runs to the exit state ([loop_body_iterates_gen]),
    [A] finishes from there.  This is the single-loop soundness with BOTH the body and the after-region
    abstracted to their realiser specs; the concrete [reloop_loop_sound] and the nested-loop case are
    instances. *)
Definition AfterRealizes (g : CFG) (exit : nat) (A : Stmt2) : Prop :=
  forall sx s', cfg_halts g exit sx s' -> seval A sx s' Normal.

Lemma loop_sound_gen : forall g hdr exit body A s sf,
  Iterates g hdr exit body ->
  AfterRealizes g exit A ->
  cfg_halts g hdr s sf ->
  seval (LSeq (LLoop body) A) s sf Normal.
Proof.
  intros g hdr exit body A s sf Hit Haft Hch.
  destruct (cfg_halts_to_n g hdr s sf Hch) as [n Hn].
  destruct (loop_body_iterates_gen g hdr exit body Hit sf n s Hn) as [sx [nx [Hloop Hexit]]].
  eapply se_seq_n; [exact Hloop | exact (Haft sx sf (cfg_halts_n_to g nx exit sx sf Hexit))].
Qed.

(** The [lift] of an acyclic [reloop] of the exit region is one such after-realiser ([reloop_correct] +
    [lift_correct] + the CFG's determinism [cfg_halts_det] pinning the final state). *)
Lemma lift_after_realizes : forall fuel g exit aft,
  reloop fuel g exit = Some aft -> AfterRealizes g exit (lift aft).
Proof.
  intros fuel g exit aft Ha sx s' Hch.
  pose proof (cfg_halts_det g exit sx s' (srun aft sx) Hch (reloop_correct fuel g exit aft Ha sx)) as Hdet.
  rewrite Hdet. apply lift_correct.
Qed.

(** ── GENERAL single-loop relooper SOUNDNESS — the open item, now CLOSED. ──
    For an ARBITRARY CFG with a loop header [hdr] and exit [exit] (NOT just [whileCFG]), whenever the
    loop-aware relooper FUNCTION succeeds ([reloop_loop hdr exit fuel g = Some S]), the structured program
    [S = LSeq (LLoop body) (lift aft)] it emits reproduces EVERY halting CFG run from [hdr].  Now a clean
    INSTANCE of [loop_sound_gen]: [reloop_b_iterates] supplies the body realiser, [lift_after_realizes] the
    after realiser.  Generalises [whileCFG_reloop_loop_correct] (the single hand-checked CFG) to the relooper
    run as an ALGORITHM on any single-loop CFG — the loop counterpart of [diamond_reloop_correct].  Axiom-free. *)
Theorem reloop_loop_sound : forall hdr exit fuel g S s sf,
  reloop_loop hdr exit fuel g = Some S ->
  cfg_halts g hdr s sf ->
  seval S s sf Normal.
Proof.
  intros hdr exit fuel g S s sf Hrl Hch.
  unfold reloop_loop in Hrl.
  destruct (reloop_b hdr exit fuel g hdr) as [body|] eqn:Hb; [|discriminate].
  destruct (reloop fuel g exit) as [aft|] eqn:Ha; [|discriminate].
  injection Hrl as <-.
  apply (loop_sound_gen g hdr exit body (lift aft) s sf
           (reloop_b_iterates hdr exit fuel g body Hb)
           (lift_after_realizes fuel g exit aft Ha) Hch).
Qed.

(** ── From ONE loop to a CHAIN of SEQUENTIAL loops. ──
    A real Go function is often [for {…}; for {…}; …; rest] — several loops in SEQUENCE, then straight-line
    code.  Its CFG is a chain: loop 1's exit IS loop 2's header, …, the last loop's exit enters the acyclic
    tail.  [reloop_chain loops final] lowers exactly that shape — one [LLoop] per loop descriptor [(h,e)]
    (header, exit), threaded so each loop's exit block begins the next region, with the [final] acyclic
    region [lift]ed at the end.  This GENERALISES [reloop_loop] (the single-loop case is [reloop_chain
    [(hdr,exit)] exit]).  [chain_ok loops final entry] is the well-formedness the lowering assumes: [entry]
    is the first loop's header and each descriptor's exit is the next region's entry (so [loop_body_iterates]
    lands each loop at the state where the next region begins). *)
Fixpoint reloop_chain (loops : list (nat * nat)) (final fuel : nat) (g : CFG) : option Stmt2 :=
  match loops with
  | [] => option_map lift (reloop fuel g final)
  | (h, e) :: rest =>
      match reloop_b h e fuel g h, reloop_chain rest final fuel g with
      | Some body, Some after => Some (LSeq (LLoop body) after)
      | _, _ => None
      end
  end.

Fixpoint chain_ok (loops : list (nat * nat)) (final entry : nat) : Prop :=
  match loops with
  | [] => entry = final
  | (h, e) :: rest => entry = h /\ chain_ok rest final e
  end.

(** SOUNDNESS for the whole chain: every halting CFG run from the chain's [entry] is reproduced by the
    structured program [reloop_chain] emits.  By induction on the chain: the empty tail is the acyclic
    [reloop] ([reloop_correct] + [lift_correct] + [cfg_halts_det], as in [reloop_loop_sound]'s after-half);
    a [(h,e)::rest] loop runs to its exit state via [loop_body_iterates], from which [chain_ok] says block
    [e] begins [rest] — so the residual run feeds the IH, and [se_seq_n] joins this loop's [LLoop] to the
    rest.  Axiom-free; proof-only. *)
Lemma reloop_chain_sound : forall loops final fuel g entry S s sf,
  chain_ok loops final entry ->
  reloop_chain loops final fuel g = Some S ->
  cfg_halts g entry s sf ->
  seval S s sf Normal.
Proof.
  intros loops. induction loops as [|[h e] rest IH];
    intros final fuel g entry S s sf Hwf Hrc Hch.
  - (* [] : entry = final, S = lift aft for the acyclic tail *)
    cbn in Hwf. subst entry. cbn in Hrc.
    destruct (reloop fuel g final) as [aft|] eqn:Ha; cbn in Hrc; [injection Hrc as <- | discriminate].
    pose proof (reloop_correct fuel g final aft Ha s) as Hac.
    pose proof (cfg_halts_det g final s sf (srun aft s) Hch Hac) as Hdet.
    rewrite Hdet. apply lift_correct.
  - (* (h,e)::rest : entry = h; this loop runs to its exit state, then the IH handles rest *)
    cbn in Hwf. destruct Hwf as [He Hrest]. subst entry. cbn in Hrc.
    destruct (reloop_b h e fuel g h) as [body|] eqn:Hb; [|discriminate].
    destruct (reloop_chain rest final fuel g) as [after|] eqn:Hrc'; [|discriminate].
    injection Hrc as <-.
    destruct (cfg_halts_to_n g h s sf Hch) as [n Hn].
    destruct (loop_body_iterates h e fuel g body sf n s Hb Hn) as [sx [nx [Hloop Hexit]]].
    eapply se_seq_n;
      [ exact Hloop
      | exact (IH final fuel g e after sx sf Hrest Hrc' (cfg_halts_n_to g nx e sx sf Hexit)) ].
Qed.

(** [reloop_chain] SUBSUMES the single-loop [reloop_loop]: the one-descriptor chain [[(hdr,exit)]] with
    final region [exit] computes EXACTLY [reloop_loop hdr exit].  So [reloop_chain_sound] is a strict
    generalisation of [reloop_loop_sound]. *)
Lemma reloop_loop_is_chain : forall hdr exit fuel g,
  reloop_chain [(hdr, exit)] exit fuel g = reloop_loop hdr exit fuel g.
Proof.
  intros hdr exit fuel g. cbn. unfold reloop_loop.
  destruct (reloop_b hdr exit fuel g hdr) as [body|]; [|reflexivity].
  destruct (reloop fuel g exit) as [aft|]; reflexivity.
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

(** ── PROPER NESTING and the inner-loop SPLIT — the kernel of nested loops. ──
    To lower a NESTED loop, one OUTER iteration ([runs_term] from the outer header) that passes through an
    inner loop must DECOMPOSE as: the inner loop runs to completion (reaching its exit block [e2]), THEN the
    outer iteration continues from [e2].  [InnerClosed g P e2] is the proper-nesting (reducibility) condition
    on a boolean predicate [P] that marks the inner region (inner blocks incl. the inner header; the inner
    exit [e2], the OUTER header and exit are NOT in [P]): every inner block's successors are the inner exit
    [e2] or again inner, and no inner block returns.  So once control is inside [P] it cannot escape to the
    outer header/exit without first hitting [e2] — exactly proper nesting. *)
Definition InnerClosed (g : CFG) (P : nat -> bool) (e2 : nat) : Prop :=
  forall l, P l = true ->
    match blk_term (g l) with
    | TRet => False
    | TGoto l' => l' = e2 \/ P l' = true
    | TIf _ a b => (a = e2 \/ P a = true) /\ (b = e2 \/ P b = true)
    end.

(** The SPLIT: an outer-relative [runs_term] entered at an inner block [l] first [runs_to] the inner exit
    [e2] (the inner loop running to completion), then [runs_term]s on from [e2] to the SAME terminal.  By
    induction on the [runs_term] derivation: [rterm_exit] (would be at outer [exit] ∉ [P]) and [rterm_back]
    (a successor = outer header ∉ [P], ∧ [h <> e2]) are IMPOSSIBLE inside the region; a [TGoto]/[TIf] either
    steps to [e2] (reached — [rt_goto]/[rt_if] then [rt_here]) or stays inner (recurse via the IH, prepending
    one [runs_to] step).  This is the runs_term decomposition the nested-loop relooper composes. *)
Lemma inner_split : forall g h e e2 P,
  InnerClosed g P e2 -> P h = false -> P e = false -> P e2 = false -> h <> e2 ->
  forall l s s' o, runs_term g h e l s s' o -> P l = true ->
  exists smid, runs_to g e2 l s smid /\ runs_term g h e e2 smid s' o.
Proof.
  intros g h e e2 P Hclosed Hh He He2 Hhe2 l s s' o Hrt.
  induction Hrt as [ s | l s Hbe Ht | l l' s s' o Hbe Ht Hnh Hrt' IH
                   | l c a b s s' o Hbe Ht Hrt' IH ]; intros Hl.
  - (* rterm_exit: l = e (outer exit), but P e = false *)
    rewrite He in Hl; discriminate.
  - (* rterm_back: successor = outer header h, forbidden by InnerClosed (h <> e2, P h = false) *)
    specialize (Hclosed l Hl); rewrite Ht in Hclosed.
    destruct Hclosed as [Hc | Hc]; congruence.
  - (* rterm_goto: step to e2 (reached) or to an inner block (recurse) *)
    assert (Hlne2 : l <> e2) by (intro Heq; subst l; rewrite He2 in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed.
    destruct Hclosed as [Hc | Hc].
    + subst l'. exists (blk_body (g l) s). split.
      * eapply rt_goto; [exact Hlne2 | exact Ht | apply rt_here].
      * exact Hrt'.
    + destruct (IH Hc) as [smid [Hru Hrest]].
      exists smid. split; [eapply rt_goto; [exact Hlne2 | exact Ht | exact Hru] | exact Hrest].
  - (* rterm_if: taken branch is e2 (reached) or inner (recurse) *)
    assert (Hlne2 : l <> e2) by (intro Heq; subst l; rewrite He2 in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed. destruct Hclosed as [Ha Hb].
    assert (Ht2 : (if c (blk_body (g l) s) then a else b) = e2
                \/ P (if c (blk_body (g l) s) then a else b) = true)
      by (destruct (c (blk_body (g l) s)); assumption).
    destruct Ht2 as [Hc | Hc].
    + exists (blk_body (g l) s). split.
      * eapply rt_if; [exact Hlne2 | exact Ht | rewrite Hc; apply rt_here].
      * rewrite Hc in Hrt'; exact Hrt'.
    + destruct (IH Hc) as [smid [Hru Hrest]].
      exists smid. split; [eapply rt_if; [exact Hlne2 | exact Ht | exact Hru] | exact Hrest].
Qed.

(** ── The INNER LOOP completing, lowered to an [LLoop] — nested-loop kernel #2. ──
    [inner_split] reduced one outer iteration to [runs_to g e2 h2 …] (the inner loop running to its exit).
    Now: that completion is reproduced by [LLoop ibody] when [ibody] realises one inner iteration
    ([Iterates g h2 e2 ibody]).  The mismatch to bridge: [runs_to] follows edges blindly (a back-edge to
    the inner header is just a goto it passes through), whereas one [Iterates] iteration STOPS at that
    back-edge — so [runs_to] = (iterate)* then (break to [e2]).  We bridge with a FUEL-INDEXED [runs_to_n]
    (the iteration count is the well-founded measure) and a per-iteration consistency lemma. *)
Inductive runs_to_n (g : CFG) (j : nat) : nat -> nat -> State -> State -> Prop :=
  | rtn_here : forall n s, runs_to_n g j (S n) j s s
  | rtn_goto : forall n l l' s sf, l <> j -> blk_term (g l) = TGoto l' ->
      runs_to_n g j n l' (blk_body (g l) s) sf -> runs_to_n g j (S n) l s sf
  | rtn_if   : forall n l c a b s sf, l <> j -> blk_term (g l) = TIf c a b ->
      runs_to_n g j n (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf ->
      runs_to_n g j (S n) l s sf.

Lemma runs_to_to_n : forall g j l s sf, runs_to g j l s sf -> exists n, runs_to_n g j n l s sf.
Proof.
  intros g j l s sf H. induction H.
  - exists 1. apply rtn_here.
  - destruct IHruns_to as [n Hn]. exists (S n). eapply rtn_goto; eassumption.
  - destruct IHruns_to as [n Hn]. exists (S n). eapply rtn_if; eassumption.
Qed.

(** Peel one [runs_to_n] step: at the target [j] the run is finished ([sf = s]); off the target a
    [TGoto]/[TIf] block drops the fuel by one to its successor. *)
Lemma rtn_here_inv : forall g j n s sf, runs_to_n g j n j s sf -> sf = s.
Proof. intros g j n s sf H. inversion H; subst; [reflexivity | congruence | congruence]. Qed.

Lemma rtn_goto_inv : forall g j n l l' s sf, l <> j -> blk_term (g l) = TGoto l' ->
  runs_to_n g j n l s sf -> exists m, n = S m /\ runs_to_n g j m l' (blk_body (g l) s) sf.
Proof.
  intros g j n l l' s sf Hlj Ht H.
  inversion H as [n0 s0 | n0 l0 l'0 s0 sf0 Hne Ht0 Hr | n0 l0 c0 a0 b0 s0 sf0 Hne Ht0 Hr]; subst.
  - congruence.
  - rewrite Ht in Ht0; injection Ht0 as <-. exists n0. split; [reflexivity | exact Hr].
  - rewrite Ht in Ht0; discriminate.
Qed.

Lemma rtn_if_inv : forall g j n l c a b s sf, l <> j -> blk_term (g l) = TIf c a b ->
  runs_to_n g j n l s sf ->
  exists m, n = S m /\ runs_to_n g j m (if c (blk_body (g l) s) then a else b) (blk_body (g l) s) sf.
Proof.
  intros g j n l c a b s sf Hlj Ht H.
  inversion H as [n0 s0 | n0 l0 l'0 s0 sf0 Hne Ht0 Hr | n0 l0 c0 a0 b0 s0 sf0 Hne Ht0 Hr]; subst.
  - congruence.
  - rewrite Ht in Ht0; discriminate.
  - rewrite Ht in Ht0; injection Ht0 as <- <- <-. exists n0. split; [reflexivity | exact Hr].
Qed.

(** CONSISTENCY: one [Iterates] iteration [runs_term g h2 e2 l …] is a PREFIX of the [runs_to_n] run that
    reaches [e2].  Either the iteration BROKE (reached [e2] — then it ends at the same state [smid]), or it
    iterated (back-edge to [h2], [Normal]) — then a STRICTLY SHORTER residual [runs_to_n] continues from
    [h2].  By induction on the iteration's [runs_term], peeling the [runs_to_n] in lock-step.  No
    determinism needed — we relate the GIVEN iteration to the GIVEN run. *)
Lemma iter_prefix : forall g h2 e2 l s s1 o,
  runs_term g h2 e2 l s s1 o ->
  forall n smid, runs_to_n g e2 n l s smid ->
  (o = Broke /\ s1 = smid)
  \/ (o = Normal /\ exists m, m < n /\ runs_to_n g e2 m h2 s1 smid).
Proof.
  intros g h2 e2 l s s1 o Hiter.
  induction Hiter as [ s | l s Hbe Ht | l l' s s' o Hbe Ht Hnh Hiter' IH
                    | l c a b s s' o Hbe Ht Hiter' IH ]; intros n smid Hrt.
  - (* rterm_exit: l = e2, o = Broke, s1 = s — the run is already at e2 *)
    left. split; [reflexivity | symmetry; exact (rtn_here_inv g e2 n s smid Hrt)].
  - (* rterm_back: TGoto h2 (inner back-edge) — Normal, residual continues from h2 *)
    right. destruct (rtn_goto_inv g e2 n l h2 s smid Hbe Ht Hrt) as [m [Hn Hres]].
    split; [reflexivity |]. exists m. subst n. split; [lia | exact Hres].
  - (* rterm_goto: same goto in the run; recurse from the successor *)
    destruct (rtn_goto_inv g e2 n l l' s smid Hbe Ht Hrt) as [m [Hn Hres]]. subst n.
    destruct (IH m smid Hres) as [[Ho Hs] | [Ho [m' [Hlt Hr']]]].
    + left. split; assumption.
    + right. split; [assumption |]. exists m'. split; [lia | exact Hr'].
  - (* rterm_if: the run takes the same branch; recurse *)
    destruct (rtn_if_inv g e2 n l c a b s smid Hbe Ht Hrt) as [m [Hn Hres]]. subst n.
    destruct (IH m smid Hres) as [[Ho Hs] | [Ho [m' [Hlt Hr']]]].
    + left. split; assumption.
    + right. split; [assumption |]. exists m'. split; [lia | exact Hr'].
Qed.

(** Hence [LLoop ibody] reproduces the inner loop's completion: by STRONG induction on the [runs_to_n]
    fuel, take one iteration (the [Iterates] hypothesis) and split it with [iter_prefix] — [Broke] ends the
    loop ([se_loop_break]), [Normal] iterates and the residual (strictly smaller fuel) feeds the IH
    ([se_loop_again]). *)
Lemma loop_to_exit_n : forall g h2 e2 ibody,
  Iterates g h2 e2 ibody ->
  forall n s smid, runs_to_n g e2 n h2 s smid -> seval (LLoop ibody) s smid Normal.
Proof.
  intros g h2 e2 ibody Hit n.
  induction n as [n IH] using lt_wf_ind. intros s smid Hrt.
  destruct (Hit s) as [s1 [o [Hiter Hsev]]].
  destruct (iter_prefix g h2 e2 h2 s s1 o Hiter n smid Hrt) as [[Ho Hs] | [Ho [m [Hlt Hres]]]].
  - subst o; subst smid. apply se_loop_break. exact Hsev.
  - subst o. eapply se_loop_again; [exact Hsev | exact (IH m Hlt s1 smid Hres)].
Qed.

Lemma loop_to_exit : forall g h2 e2 ibody,
  Iterates g h2 e2 ibody ->
  forall s smid, runs_to g e2 h2 s smid -> seval (LLoop ibody) s smid Normal.
Proof.
  intros g h2 e2 ibody Hit s smid Hrt.
  destruct (runs_to_to_n g e2 h2 s smid Hrt) as [n Hn].
  exact (loop_to_exit_n g h2 e2 ibody Hit n s smid Hn).
Qed.

(** ── The WHOLE-RUN inner-loop split — the toolkit piece the nested ASSEMBLY needs. ──
    [inner_split] is the per-iteration view ([runs_term]).  But assembling a nested loop needs the
    WHOLE-RUN view: the outer loop's body realiser is only definable WHEN the run terminates (a nested
    body's one iteration includes running the inner loop to completion, which need not terminate in
    general — so an UNCONDITIONAL [Iterates] over a nested body is false).  Under a terminating run
    ([cfg_halts_n], fuel-indexed for the outer strong induction) the inner loop DOES complete, and we can
    extract it: from an inner block the run first [runs_to] the inner exit [e2], then [cfg_halts_n]
    continues from [e2] at NO MORE fuel.  The fuel bound [m <= n] is what lets the outer loop's strong
    induction recurse on the post-inner-loop continuation.  Simpler than [inner_split] (no outer header/
    exit, no back-edge case): [InnerClosed] forbids a [TRet] in the region, so the run cannot halt inside
    it — it must leave via [e2]. *)
Lemma inner_split_cfg_n : forall g e2 P,
  InnerClosed g P e2 -> P e2 = false ->
  forall n l s sf, cfg_halts_n g n l s sf -> P l = true ->
  exists smid m, m <= n /\ runs_to g e2 l s smid /\ cfg_halts_n g m e2 smid sf.
Proof.
  intros g e2 P Hclosed He2 n l s sf Hch.
  induction Hch as [n l s Ht | n l l' s sf Ht Hch' IH | n l c a b s sf Ht Hch' IH]; intros Hl.
  - (* chn_ret: a TRet inside the region is forbidden by InnerClosed *)
    specialize (Hclosed l Hl); rewrite Ht in Hclosed; destruct Hclosed.
  - (* chn_goto: step to e2 (reached) or to an inner block (recurse) *)
    assert (Hlne2 : l <> e2) by (intro Heq; subst l; rewrite He2 in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed. destruct Hclosed as [Hc | Hc].
    + subst l'. exists (blk_body (g l) s), n. split; [lia | split].
      * eapply rt_goto; [exact Hlne2 | exact Ht | apply rt_here].
      * exact Hch'.
    + destruct (IH Hc) as [smid [m [Hle [Hru Hres]]]].
      exists smid, m. split; [lia | split; [eapply rt_goto; [exact Hlne2 | exact Ht | exact Hru] | exact Hres]].
  - (* chn_if: taken branch is e2 (reached) or inner (recurse) *)
    assert (Hlne2 : l <> e2) by (intro Heq; subst l; rewrite He2 in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed. destruct Hclosed as [Ha Hb].
    assert (Ht2 : (if c (blk_body (g l) s) then a else b) = e2
                \/ P (if c (blk_body (g l) s) then a else b) = true)
      by (destruct (c (blk_body (g l) s)); assumption).
    destruct Ht2 as [Hc | Hc].
    + exists (blk_body (g l) s), n. split; [lia | split].
      * eapply rt_if; [exact Hlne2 | exact Ht | rewrite Hc; apply rt_here].
      * rewrite Hc in Hch'; exact Hch'.
    + destruct (IH Hc) as [smid [m [Hle [Hru Hres]]]].
      exists smid, m. split; [lia | split; [eapply rt_if; [exact Hlne2 | exact Ht | exact Hru] | exact Hres]].
Qed.

(** A [runs_to] already AT its target makes no step. *)
Lemma runs_to_here_inv : forall g j s sf, runs_to g j j s sf -> sf = s.
Proof. intros g j s sf H. inversion H; subst; [reflexivity | congruence | congruence]. Qed.

(** ── The CONVERSE of [inner_split]: SPLICE a completed inner loop into an outer iteration's [runs_term]. ──
    [inner_split] takes an outer-iteration [runs_term] and pulls the inner loop's completion OUT as a
    [runs_to].  [inner_join] runs the other way: given the inner loop has completed ([runs_to g ie l s smid]
    — control went from inner block [l] to the inner exit [ie]), it reconstructs the OUTER iteration's
    [runs_term] across that span — traversing the inner region (each [runs_to] step becomes an outer
    [rterm_goto]/[rterm_if]) and finishing with the [ie]→[h] BACK-EDGE ([rterm_back], one outer iteration).
    [InnerClosed] keeps the path inside [P] (so no [rterm_back]/[rterm_exit] fires early), and the inner exit
    [ie] back-edges to the outer header [h].  This is the piece needed to EXPRESS a nested outer iteration as
    a [runs_term] — i.e. to build [Iterates]/[IteratesC] for a body wrapping an inner [LLoop], the path to
    arbitrary-depth nesting. *)
Lemma inner_join : forall g h e ie P,
  InnerClosed g P ie -> P h = false -> P e = false -> P ie = false ->
  ie <> e -> ie <> h -> blk_term (g ie) = TGoto h ->
  forall l s smid, runs_to g ie l s smid -> P l = true ->
  runs_term g h e l s (blk_body (g ie) smid) Normal.
Proof.
  intros g h e ie P Hclosed Ph Pe Pie Hiee Hieh Hiet l s smid Hrt.
  induction Hrt as [ s | l l' s sf Hlne Ht Hr IH | l c a b s sf Hlne Ht Hr IH ]; intros Hl.
  - (* rt_here: l = ie, impossible since P ie = false *)
    rewrite Pie in Hl; discriminate.
  - (* rt_goto: step to ie (fire the back-edge) or stay inner (recurse) *)
    assert (Hle : l <> e) by (intro Heq; subst l; rewrite Pe in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed. destruct Hclosed as [Hc | Hc].
    + subst l'. pose proof (runs_to_here_inv g ie (blk_body (g l) s) sf Hr) as Hsm. subst sf.
      eapply rterm_goto; [exact Hle | exact Ht | exact Hieh |].
      apply rterm_back; [exact Hiee | exact Hiet].
    + assert (Hl'h : l' <> h) by (intro Heq; subst l'; rewrite Ph in Hc; discriminate).
      eapply rterm_goto; [exact Hle | exact Ht | exact Hl'h | exact (IH Hc)].
  - (* rt_if: taken branch is ie (back-edge) or inner (recurse) *)
    assert (Hle : l <> e) by (intro Heq; subst l; rewrite Pe in Hl; discriminate).
    specialize (Hclosed l Hl); rewrite Ht in Hclosed. destruct Hclosed as [Ha Hb].
    assert (Ht2 : (if c (blk_body (g l) s) then a else b) = ie
                \/ P (if c (blk_body (g l) s) then a else b) = true)
      by (destruct (c (blk_body (g l) s)); assumption).
    destruct Ht2 as [Hc | Hc].
    + rewrite Hc in Hr. pose proof (runs_to_here_inv g ie (blk_body (g l) s) sf Hr) as Hsm. subst sf.
      eapply rterm_if; [exact Hle | exact Ht |]. rewrite Hc.
      apply rterm_back; [exact Hiee | exact Hiet].
    + eapply rterm_if; [exact Hle | exact Ht | exact (IH Hc)].
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

(** ════════════════════════════════════════════════════════════════════════════════════════════════
    NESTED LOOPS — the canonical doubly-nested loop, lowered through the compositional kernels.
    ════════════════════════════════════════════════════════════════════════════════════════════════
    The two kernels — [inner_split]/[inner_split_cfg_n] (decompose a run that passes through an inner loop)
    and [loop_to_exit] (lower the inner loop to an [LLoop]) — assemble into END-TO-END soundness for a
    real nested loop.  [nestCFG] is the canonical doubly-nested while (parametric in its block functions,
    like [whileCFG] but two-level): outer header 0 (enter inner / exit to 4), inner header 1 (inner body 2 /
    inner exit 3), inner body 2 (back-edge to 1), block 3 (back-edge to outer header 0), outer exit 4.  Its
    lowering nests an [LLoop] inside an [LLoop]. *)
Definition nestCFG (f0 f1 f2 f3 f4 : State -> State) (c0 c1 : State -> bool) : CFG :=
  fun l => match l with
           | 0 => mkBlk f0 (TIf c0 1 4)
           | 1 => mkBlk f1 (TIf c1 2 3)
           | 2 => mkBlk f2 (TGoto 1)
           | 3 => mkBlk f3 (TGoto 0)
           | _ => mkBlk f4 TRet
           end.

Definition nestInner (f1 f2 : State -> State) (c1 : State -> bool) : Stmt2 :=
  LSeq (LBody f1) (LIf c1 (LBody f2) LBreak).

Definition nestOuter (f0 f1 f2 f3 : State -> State) (c0 c1 : State -> bool) : Stmt2 :=
  LSeq (LBody f0) (LIf c0 (LSeq (LLoop (nestInner f1 f2 c1)) (LBody f3)) LBreak).

Definition nestP (l : nat) : bool := orb (Nat.eqb l 1) (Nat.eqb l 2).

(** The inner body is exactly [reloop_b]'s acyclic lowering of the inner loop, so it realises one inner
    iteration. *)
Lemma nest_inner_iter : forall f0 f1 f2 f3 f4 c0 c1,
  Iterates (nestCFG f0 f1 f2 f3 f4 c0 c1) 1 3 (nestInner f1 f2 c1).
Proof.
  intros. apply (reloop_b_iterates 1 3 5 (nestCFG f0 f1 f2 f3 f4 c0 c1) (nestInner f1 f2 c1)).
  reflexivity.
Qed.

(** The inner region {1,2} is properly nested with exit 3. *)
Lemma nest_inner_closed : forall f0 f1 f2 f3 f4 c0 c1,
  InnerClosed (nestCFG f0 f1 f2 f3 f4 c0 c1) nestP 3.
Proof.
  intros f0 f1 f2 f3 f4 c0 c1 l Hl. unfold nestP in Hl.
  destruct l as [|[|[|l]]]; cbn in Hl |- *; try discriminate.
  - split; [right; reflexivity | left; reflexivity].
  - right; reflexivity.
Qed.

Lemma chn_ret_inv : forall g n l s sf,
  blk_term (g l) = TRet -> cfg_halts_n g n l s sf -> sf = blk_body (g l) s.
Proof.
  intros g n l s sf Ht H.
  inversion H as [n0 l0 s0 Ht0 | n0 l0 l' s0 sf0 Ht0 Hc | n0 l0 c0 a0 b0 s0 sf0 Ht0 Hc]; subst.
  - reflexivity.
  - rewrite Ht in Ht0; discriminate.
  - rewrite Ht in Ht0; discriminate.
Qed.

(** ── GENERAL depth-2 nesting: ANY CFG with one properly-nested inner loop. ──
    Abstracting [nest_outer_loop] off the concrete [nestCFG]: for ANY CFG [g] whose outer header [h]
    branches ([TIf c0 ih e]) into a properly-nested inner loop (header [ih], exit [ie], inner region [P]
    with [InnerClosed g P ie]) or to the outer exit [e], and whose inner-exit block [ie] back-edges to [h],
    the outer [LLoop] runs to [e].  The INNER loop is arbitrary — ANYTHING with an iteration realiser
    [Iterates g ih ie ibody] (its own lowering): the body need only be an iteration realiser, so this covers
    every acyclic-bodied inner loop in general position, not just [nestCFG]'s.  Proof: [loop_body_iterates]
    for a nested body — strong induction on the run's fuel ([lt_wf_ind]); one outer iteration breaks (c0
    false ⇒ [se_loop_break]) or runs the inner loop ([inner_split_cfg_n] extracts [runs_to g ie ih] from the
    terminating run at residual fuel ≤; [loop_to_exit] makes it an inner [LLoop]), takes the [ie]→[h]
    back-edge, and the IH handles the next iteration at strictly smaller fuel ([se_loop_again]). *)
Lemma nested_outer_loop_gen : forall g h e ih ie c0 bh bie ibody P,
  blk_term (g h) = TIf c0 ih e -> blk_body (g h) = bh ->
  blk_term (g ie) = TGoto h -> blk_body (g ie) = bie ->
  InnerClosed g P ie -> P ih = true -> P ie = false ->
  Iterates g ih ie ibody ->
  forall n s sf, cfg_halts_n g n h s sf ->
  exists sx nx,
    seval (LLoop (LSeq (LBody bh) (LIf c0 (LSeq (LLoop ibody) (LBody bie)) LBreak))) s sx Normal
    /\ cfg_halts_n g nx e sx sf.
Proof.
  intros g h e ih ie c0 bh bie ibody P Hht Hhb Hiet Hieb Hclosed Pih Pie Hit.
  intro n. induction n as [n IH] using lt_wf_ind. intros s sf Hch.
  destruct (chn_if_inv g n h c0 ih e s sf Hht Hch) as [m [Hn Hm]].
  rewrite Hhb in Hm.
  destruct (c0 (bh s)) eqn:Ec0.
  - (* enter the inner loop (Hm reads block ih up to iota) *)
    destruct (inner_split_cfg_n g ie P Hclosed Pie m ih (bh s) sf Hm Pih)
      as [smid [m1 [Hle1 [Hru Hcf_ie]]]].
    pose proof (loop_to_exit g ih ie ibody Hit (bh s) smid Hru) as Hin.
    destruct (chn_goto_inv g m1 ie h smid sf Hiet Hcf_ie) as [m2 [Hm1 Hcf_h]].
    rewrite Hieb in Hcf_h.
    assert (Hlt : m2 < n) by lia.
    destruct (IH m2 Hlt (bie smid) sf Hcf_h) as [sx [nx [Hout Hcfx]]].
    exists sx, nx. split; [| exact Hcfx].
    eapply se_loop_again; [| exact Hout].
    eapply se_seq_n; [apply se_body |].
    eapply se_if_t; [exact Ec0 |].
    eapply se_seq_n; [exact Hin | apply se_body].
  - (* the outer loop breaks at the exit *)
    exists (bh s), m. split; [| exact Hm].
    apply se_loop_break.
    eapply se_seq_n; [apply se_body |].
    eapply se_if_f; [exact Ec0 |].
    apply se_break.
Qed.

(** [nestCFG]'s outer loop is the instance of the general lemma — the concrete 5-block witness now FOLLOWS
    from [nested_outer_loop_gen]. *)
Lemma nest_outer_loop : forall f0 f1 f2 f3 f4 c0 c1 n s sf,
  cfg_halts_n (nestCFG f0 f1 f2 f3 f4 c0 c1) n 0 s sf ->
  exists sx nx, seval (LLoop (nestOuter f0 f1 f2 f3 c0 c1)) s sx Normal
              /\ cfg_halts_n (nestCFG f0 f1 f2 f3 f4 c0 c1) nx 4 sx sf.
Proof.
  intros f0 f1 f2 f3 f4 c0 c1 n s sf Hch.
  exact (nested_outer_loop_gen (nestCFG f0 f1 f2 f3 f4 c0 c1) 0 4 1 3 c0 f0 f3
           (nestInner f1 f2 c1) nestP
           eq_refl eq_refl eq_refl eq_refl
           (nest_inner_closed f0 f1 f2 f3 f4 c0 c1) eq_refl eq_refl
           (nest_inner_iter f0 f1 f2 f3 f4 c0 c1) n s sf Hch).
Qed.

(** END-TO-END NESTED-LOOP SOUNDNESS: every halting run of the doubly-nested CFG is reproduced by the
    nested [LLoop]-in-[LLoop] structured program.  The outer [LLoop] runs to block 4 ([nest_outer_loop]),
    whose [TRet] pins the final state ([chn_ret_inv]); the trailing [LBody f4] finishes.  Proven entirely
    THROUGH the compositional kernels — validating that [inner_split]/[inner_split_cfg_n] + [loop_to_exit] +
    the loop machinery assemble for real nesting. *)
Theorem nested_loop_sound : forall f0 f1 f2 f3 f4 c0 c1 s sf,
  cfg_halts (nestCFG f0 f1 f2 f3 f4 c0 c1) 0 s sf ->
  seval (LSeq (LLoop (nestOuter f0 f1 f2 f3 c0 c1)) (LBody f4)) s sf Normal.
Proof.
  intros f0 f1 f2 f3 f4 c0 c1 s sf Hch.
  set (g := nestCFG f0 f1 f2 f3 f4 c0 c1).
  destruct (cfg_halts_to_n g 0 s sf Hch) as [n Hn].
  destruct (nest_outer_loop f0 f1 f2 f3 f4 c0 c1 n s sf Hn) as [sx [nx [Hloop Hcfx]]].
  assert (T4t : blk_term (g 4) = TRet) by reflexivity.
  assert (T4b : blk_body (g 4) = f4) by reflexivity.
  pose proof (chn_ret_inv g nx 4 sx sf T4t Hcfx) as Hsf. rewrite T4b in Hsf.
  eapply se_seq_n; [exact Hloop | rewrite Hsf; apply se_body].
Qed.

End Relooper.
