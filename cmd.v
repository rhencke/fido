(** Deep-embedded command tree [Cmd] — the operational FOUNDATION for review #6 #22 (one
    authoritative semantics) and #12 (defer as a REAL construct).

    Why a deep embedding.  The shallow [IO := World -> Outcome] cannot REIFY control: a deferred
    [IO unit] cannot be stored in [World] (it would put [World] left of an arrow in its OWN
    definition — a non-strictly-positive occurrence Coq rejects), and there is no syntax to give an
    authoritative interleaving/step semantics.  So [defer] and the unified concurrency calculus need
    a DEEP embedding — [Cmd] is the SYNTAX of a program.

    Continuation-passing shape.  A free-monad [Bind : Cmd A -> (A -> Cmd B) -> Cmd B] node makes every
    interpreter NON-structural (it must run [k a] on a non-subterm).  Instead each effect node carries
    its CONTINUATION, so [cbind] (append the continuation) and the interpreters are genuine structural
    [Fixpoint]s.

    SLICE 1 (this file, to grow): the syntax for output/panic, [cbind], a faithful denotation
    [denote : Cmd A -> IO A] back to the shallow model (a [Cmd]-written program runs EXACTLY as the
    shallow one — so a migration is golden byte-identical), and the monad laws + the fact that [denote]
    is a monad morphism.  Subsequent slices add [catch], heap/channel ops, [defer] with its func-scope
    stack (the #12 fix), and the small-step interleaving semantics (the #22 unification). *)
From Fido Require Import preamble.
From Stdlib Require Import List.
Import ListNotations.

(** The program syntax.  [COut] = a [print]/[println] of [xs] THEN the continuation; [CPan] = panic
    (no continuation — it short-circuits).  More effect nodes (refs, channels, catch, defer) follow. *)
Inductive Cmd (A : Type) : Type :=
  | CRet : A -> Cmd A
  | COut : bool -> list GoAny -> Cmd A -> Cmd A
  | CPan : GoAny -> Cmd A.
Arguments CRet {A} _.
Arguments COut {A} _ _ _.
Arguments CPan {A} _.

(** [cbind c k] — sequencing, by appending [k] to [c]'s continuations.  STRUCTURAL on [c], so a real
    [Fixpoint] (the whole point of the CPS shape). *)
Fixpoint cbind {A B} (c : Cmd A) (k : A -> Cmd B) : Cmd B :=
  match c with
  | CRet a => k a
  | COut b xs c' => COut b xs (cbind c' k)
  | CPan v => CPan v
  end.

(** The shallow output op (identical to [print]/[println] in builtins.v — appends to the [w_output]
    trace, the observable that makes equality Go-observational, review #12). *)
Definition out (b : bool) (xs : list GoAny) : IO unit := fun w => ORet tt (w_log b xs w).

(** Denotation back to the shallow model: structural, so a [Cmd] program's runtime behaviour IS the
    corresponding shallow [IO] — the migration preserves observable behaviour exactly. *)
Fixpoint denote {A} (c : Cmd A) : IO A :=
  match c with
  | CRet a => ret a
  | COut b xs c' => bind (out b xs) (fun _ => denote c')
  | CPan v => panic v
  end.

(** ---- The deep syntax is a LAWFUL monad ---- *)
Lemma cbind_ret_l : forall {A B} (a : A) (k : A -> Cmd B), cbind (CRet a) k = k a.
Proof. reflexivity. Qed.
Lemma cbind_ret_r : forall {A} (c : Cmd A), cbind c (fun a => CRet a) = c.
Proof. induction c; cbn; try reflexivity. rewrite IHc; reflexivity. Qed.
Lemma cbind_assoc : forall {A B C} (c : Cmd A) (k : A -> Cmd B) (h : B -> Cmd C),
  cbind (cbind c k) h = cbind c (fun a => cbind (k a) h).
Proof. intros. induction c; cbn; try reflexivity. rewrite IHc; reflexivity. Qed.

(** ---- [denote] is a MONAD MORPHISM (observationally): the deep program's runtime behaviour is its
    shallow denotation, so reasoning/extraction can move between the two ---- *)
Lemma denote_ret : forall {A} (a : A), denote (CRet a) = ret a.
Proof. reflexivity. Qed.
Lemma denote_bind : forall {A B} (c : Cmd A) (k : A -> Cmd B),
  denote (cbind c k) =io= bind (denote c) (fun a => denote (k a)).
Proof.
  intros A B c k. induction c; cbn.
  - rewrite bind_ret_l. reflexivity.
  - rewrite bind_assoc. setoid_rewrite IHc. reflexivity.
  - rewrite bind_panic_l. reflexivity.
Qed.
