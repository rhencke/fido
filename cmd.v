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
  | CPan : GoAny -> Cmd A
  | CDfr : Cmd unit -> Cmd A -> Cmd A.   (* [defer d]; [d] runs at function-scope return (review #12) *)
Arguments CRet {A} _.
Arguments COut {A} _ _ _.
Arguments CPan {A} _.
Arguments CDfr {A} _ _.

(** The deferred action [Cmd unit] makes [A] a NON-uniform parameter, so Coq's auto-generated [Cmd_ind]
    has a POLYMORPHIC motive ([forall A, Cmd A -> Prop]) and a spurious induction hypothesis for the
    deferred — which is ill-typed for motives where [A] is load-bearing (e.g. [cbind_assoc], whose [k :
    A -> Cmd B] pins [A]).  But [cbind]/[denote] treat the deferred OPAQUELY (they recurse only into the
    continuation), so this MONOMORPHIC principle — recurse into the continuation, leave the deferred
    abstract — is exactly the right tool and keeps every structural proof a clean four-case induction. *)
Fixpoint Cmd_rect' (A : Type) (P : Cmd A -> Type)
  (fret : forall a, P (CRet a)) (fout : forall b xs c', P c' -> P (COut b xs c'))
  (fpan : forall v, P (CPan v)) (fdfr : forall d c', P c' -> P (CDfr d c'))
  (c : Cmd A) : P c :=
  match c with
  | CRet a => fret a
  | COut b xs c' => fout b xs c' (Cmd_rect' A P fret fout fpan fdfr c')
  | CPan v => fpan v
  | CDfr d c' => fdfr d c' (Cmd_rect' A P fret fout fpan fdfr c')
  end.
Definition Cmd_ind' (A : Type) (P : Cmd A -> Prop) := Cmd_rect' A P.

(** [cbind c k] — sequencing, by appending [k] to [c]'s continuations.  STRUCTURAL on [c], so a real
    [Fixpoint] (the whole point of the CPS shape). *)
Fixpoint cbind {A B} (c : Cmd A) (k : A -> Cmd B) : Cmd B :=
  match c with
  | CRet a => k a
  | COut b xs c' => COut b xs (cbind c' k)
  | CPan v => CPan v
  | CDfr d c' => CDfr d (cbind c' k)
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
  | CDfr _ c' => denote c'   (* the SHALLOW reading DROPS the deferred action — exactly the [defer_call]
                                no-op the review (#12) flags as a bug.  [run_cmd] below is the FAITHFUL
                                operational semantics that actually runs it; their difference IS the bug. *)
  end.

(** ---- The deep syntax is a LAWFUL monad ---- *)
Lemma cbind_ret_l : forall {A B} (a : A) (k : A -> Cmd B), cbind (CRet a) k = k a.
Proof. reflexivity. Qed.
Lemma cbind_ret_r : forall {A} (c : Cmd A), cbind c (fun a => CRet a) = c.
Proof.
  induction c as [a | b xs c' IH | v | d c' IH] using Cmd_ind'; cbn.
  - reflexivity.
  - rewrite IH; reflexivity.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.
Lemma cbind_assoc : forall {A B C} (c : Cmd A) (k : A -> Cmd B) (h : B -> Cmd C),
  cbind (cbind c k) h = cbind c (fun a => cbind (k a) h).
Proof.
  intros A B C c k h. induction c as [a | b xs c' IH | v | d c' IH] using Cmd_ind'; cbn.
  - reflexivity.
  - rewrite IH; reflexivity.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** ---- [denote] is a MONAD MORPHISM (observationally): the deep program's runtime behaviour is its
    shallow denotation, so reasoning/extraction can move between the two ---- *)
Lemma denote_ret : forall {A} (a : A), denote (CRet a) = ret a.
Proof. reflexivity. Qed.
Lemma denote_bind : forall {A B} (c : Cmd A) (k : A -> Cmd B),
  denote (cbind c k) =io= bind (denote c) (fun a => denote (k a)).
Proof.
  intros A B c k. induction c as [a | b xs c' IH | v | d c' IH] using Cmd_ind'; cbn.
  - rewrite bind_ret_l. reflexivity.
  - rewrite bind_assoc. setoid_rewrite IH. reflexivity.
  - rewrite bind_panic_l. reflexivity.
  - exact IH.
Qed.

(** ---- The AUTHORITATIVE operational interpreter — [defer] is no longer a no-op (review #12) ----

    [denote] above gives the SHALLOW reading (defers dropped); [run_cmd] here is the faithful semantics
    that actually runs them at function-scope return.  The difference between the two on a deferred
    program is EXACTLY the #12 bug, now fixed by taking [run_cmd] as authoritative. *)
Definition oc_world {A} (oc : Outcome A) : World := match oc with ORet _ w => w | OPanic _ w => w end.
Definition oc_set_world {A} (oc : Outcome A) (w : World) : Outcome A :=
  match oc with ORet a _ => ORet a w | OPanic v _ => OPanic v w end.

(** [go c w] runs [c]'s body, ACCUMULATING the deferred actions (without running them yet).  Structural
    on [c] — the CPS continuations are subterms, so no fuel needed here. *)
Fixpoint go {A} (c : Cmd A) (w : World) : Outcome A * list (Cmd unit) :=
  match c with
  | CRet a => (ORet a w, nil)
  | COut b xs c' => go c' (w_log b xs w)
  | CPan v => (OPanic v w, nil)
  | CDfr d c' => let '(oc, ds) := go c' w in (oc, ds ++ (d :: nil))
  end.

(** Project an [Outcome A] to [Outcome unit], keeping its panic value and world — the "active panic"
    carrier threaded through defer unwinding. *)
Definition oc_unit {A} (oc : Outcome A) : Outcome unit :=
  match oc with ORet _ w => ORet tt w | OPanic v w => OPanic v w end.

(** [run_defers fuel ds acc] runs EVERY deferred action in [ds] — [go] APPENDS each, so the head is the
    LAST-deferred = runs FIRST (LIFO, as Go) — threading the "active panic" in [acc : Outcome unit]
    ([ORet] = none in flight, [OPanic v] = panic [v] in flight).  Go semantics, faithfully: each deferred
    action runs as its OWN func scope (its nested defers run, SEEDED by its body's outcome [oc_d]); if its
    net outcome PANICS, that panic REPLACES the active one — but the REMAINING (older) defers STILL RUN
    regardless, accumulating their effects.  So the final panic is the LAST one raised during unwinding,
    and EVERY defer's effects happen.

    REVIEW P0 (the bug this replaces): the earlier version STOPPED at the first panicking defer and
    returned its panic WITHOUT running the older defers [ds'] — Go continues the whole LIFO stack, a newer
    panic merely replacing the active one.  Skipping older defers permitted FALSE heap / output /
    resource-release proofs (a deferred [Close]/unlock/log after a panicking defer was provably dropped).
    Fuel bounds the deferred-of-deferred nesting (the accumulation is not structural). *)
Fixpoint run_defers (fuel : nat) (ds : list (Cmd unit)) (acc : Outcome unit) : option (Outcome unit) :=
  match fuel with
  | O => None
  | S n =>
    match ds with
    | nil => Some acc
    | d :: ds' =>
        let '(oc_d, ds_d) := go d (oc_world acc) in
        match run_defers n ds_d oc_d with             (* d's net outcome: its body THEN its own nested defers *)
        | None => None
        | Some net_d =>
            let acc' := match net_d with
                        | OPanic v' w' => OPanic v' w'        (* d panicked: REPLACE the active panic *)
                        | ORet _ w'    => oc_set_world acc w' (* d returned: KEEP the active panic, advance world *)
                        end in
            run_defers n ds' acc'                     (* ...then ALWAYS run the older defers *)
        end
    end
  end.

(** Full func-scope run: the body, THEN its defers (LIFO), keeping the body's value or propagating a
    deferred panic.  [defer] is now FAITHFUL — the review #12 no-op is gone. *)
Definition run_cmd (fuel : nat) {A} (c : Cmd A) (w : World) : option (Outcome A) :=
  let '(oc, ds) := go c w in
  match run_defers fuel ds (oc_unit oc) with    (* seed the active panic with the body's own outcome *)
  | Some (ORet _ w') => Some (oc_set_world oc w')
  | Some (OPanic v w') => Some (OPanic v w')
  | None => None
  end.

(** [no_defer c] — [c] registers no [CDfr]: a straight-line output/panic/return command.  A pure [Cmd]
    predicate, so it lives here (cmd.v), shared by GoSem (executable totality: [go] accumulates no defers)
    and cmd_unified.v (its no_defer fragment bridges 1-for-1 onto [unified.v]'s [ustep]; DEFER-bearing commands
    are bridged by [bridge_flat_agrees]). *)
Fixpoint no_defer (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => no_defer c' | CPan _ => true | CDfr _ _ => false
  end.

(** [cmd_no_panic c] — [c] has NO [CPan] node ANYWHERE (body or any deferred action): it can never end in an
    [OPanic] outcome.  A pure [Cmd] predicate (sibling of [no_defer]), so it lives here in cmd.v — the SINGLE
    authority; consumed by GoSemSafe (the panic-free safety property); never a second copy. *)
Fixpoint cmd_no_panic (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => cmd_no_panic c' | CPan _ => false | CDfr d c' => cmd_no_panic d && cmd_no_panic c'
  end.

(** ---- The #12 fix, demonstrated ---- *)

(** [defer println(a); defer println(b); return] prints b THEN a (LIFO at return), exactly as Go. *)
Example defer_runs_lifo : forall (a b : GoAny) (w : World),
  run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt))) w
    = Some (ORet tt (w_log true (a :: nil) (w_log true (b :: nil) w))).
Proof. reflexivity. Qed.

(** The SHALLOW denotation of the SAME program runs NEITHER deferred (output unchanged) — the [defer_call]
    no-op the review flags.  The contrast with [defer_runs_lifo] IS review #12, made explicit and fixed. *)
Example defer_shallow_drops : forall (a b : GoAny) (w : World),
  run_io (denote (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt)))) w
    = ORet tt w.
Proof. reflexivity. Qed.

(** Defers run even when the body PANICS (Go semantics): the deferred [println(a)] still happens, then the
    panic propagates. *)
Example defer_runs_on_panic : forall (a v : GoAny) (w : World),
  run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CPan v) : Cmd unit) w
    = Some (OPanic v (w_log true (a :: nil) w)).
Proof. reflexivity. Qed.

(** THE P0 FIX, LOCKED: a NEWER defer panics (runs FIRST in LIFO) — the OLDER deferred [println(a)] STILL
    RUNS (its output [w_log a] appears) and the panic propagates.  The pre-fix interpreter STOPPED at the
    panicking defer and returned [OPanic v w] with NO [w_log a] — a provably-dropped deferred effect. *)
Example defer_older_runs_after_newer_panics : forall (a v : GoAny) (w : World),
  run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (CPan v) (CRet tt)) : Cmd unit) w
    = Some (OPanic v (w_log true (a :: nil) w)).
Proof. reflexivity. Qed.

(** Two panicking defers: the LAST to run (the EARLIER-registered [v1], deepest in LIFO) wins, replacing
    the newer [v2] — exactly Go's "a later panic during unwinding replaces the active one". *)
Example defer_last_panic_wins : forall (v1 v2 : GoAny) (w : World),
  run_cmd 5 (CDfr (CPan v1) (CDfr (CPan v2) (CRet tt)) : Cmd unit) w
    = Some (OPanic v1 w).
Proof. reflexivity. Qed.
