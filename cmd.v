(** Deep-embedded command tree [Cmd] — the operational FOUNDATION (one
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

    THIS FILE: the syntax for output/panic/defer + the typed HEAP pair ([CWrite]/[CRead] — tag-preserving
    writes, ABSENT on unallocated access), [cbind] + the monad laws (over [CmdEq]), and the
    AUTHORITATIVE operational interpreter [run_cmd] — which runs the body THEN its [defer] stack (LIFO,
    func-scope return, on panic too; the #12 fix).  There is NO shallow [Cmd -> IO] reading: a sequential
    [World -> Outcome] cannot run a func-scoped defer at return, so [run_cmd] is the ONLY semantics for a
    [Cmd] (a shallow drop/no-op would silently erase a deferred effect).  Channel ops and
    [catch] are future slices (plans/bridge-effects.md). *)
From Fido Require Import preamble.
From Stdlib Require Import List Lia.
Import ListNotations.

(** The program syntax.  [COut] = a [print]/[println] of [xs] THEN the continuation; [CPan] = panic
    (no continuation — it short-circuits); [CDfr] = defer; [CWrite]/[CRead] = the typed heap pair.
    Channel effect nodes and [catch] follow in later slices. *)
Inductive Cmd (A : Type) : Type :=
  | CRet : A -> Cmd A
  | COut : bool -> list GoAny -> Cmd A -> Cmd A
  | CPan : GoAny -> Cmd A
  | CDfr : Cmd unit -> Cmd A -> Cmd A    (* [defer d]; [d] runs at function-scope return *)
  (* the HEAP pair (bridge-effects slice 2; appended LAST so existing destruct/induction
     bullet lists keep their order).  [CRead] is the syntax's first value-BINDING
     constructor — its continuation is a function, which shapes everything below:
     structural booleans cannot scan under it, and extensional facts about it need
     [CmdEq], never an axiom. *)
  | CWrite : nat -> GoAny -> Cmd A -> Cmd A   (* *l = v; then k — tag-PRESERVING (typed cell) *)
  | CRead  : nat -> (GoAny -> Cmd A) -> Cmd A.  (* x := *l; then k x *)
Arguments CRet {A} _.
Arguments COut {A} _ _ _.
Arguments CPan {A} _.
Arguments CDfr {A} _ _.
Arguments CWrite {A} _ _ _.
Arguments CRead {A} _ _.

(** The deferred action [Cmd unit] makes [A] a NON-uniform parameter, so Coq's auto-generated [Cmd_ind]
    has a POLYMORPHIC motive ([forall A, Cmd A -> Prop]) and a spurious induction hypothesis for the
    deferred — which is ill-typed for motives where [A] is load-bearing (e.g. [cbind_assoc], whose [k :
    A -> Cmd B] pins [A]).  But [cbind] treats the deferred OPAQUELY (it recurses only into the
    continuation), so this MONOMORPHIC principle — recurse into the continuation, leave the deferred
    abstract — is exactly the right tool and keeps every structural proof a clean four-case induction. *)
Fixpoint Cmd_rect' (A : Type) (P : Cmd A -> Type)
  (fret : forall a, P (CRet a)) (fout : forall b xs c', P c' -> P (COut b xs c'))
  (fpan : forall v, P (CPan v)) (fdfr : forall d c', P c' -> P (CDfr d c'))
  (fwr : forall l v c', P c' -> P (CWrite l v c'))
  (frd : forall l f, (forall x, P (f x)) -> P (CRead l f))
  (c : Cmd A) : P c :=
  match c with
  | CRet a => fret a
  | COut b xs c' => fout b xs c' (Cmd_rect' A P fret fout fpan fdfr fwr frd c')
  | CPan v => fpan v
  | CDfr d c' => fdfr d c' (Cmd_rect' A P fret fout fpan fdfr fwr frd c')
  | CWrite l v c' => fwr l v c' (Cmd_rect' A P fret fout fpan fdfr fwr frd c')
  | CRead l f => frd l f (fun x => Cmd_rect' A P fret fout fpan fdfr fwr frd (f x))
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
  | CWrite l v c' => CWrite l v (cbind c' k)
  | CRead l f => CRead l (fun x => cbind (f x) k)
  end.


(** ---- The deep syntax is a LAWFUL monad — up to EXTENSIONAL command equivalence ----

    [CRead]'s continuation is a FUNCTION, so the right-unit and associativity laws hold
    POINTWISE under the binder; Coq's [eq] cannot see that without functional
    extensionality, and the model's trust base stays EMPTY — so the laws are stated over
    [CmdEq], the congruence that compares read continuations pointwise (deferred bodies
    and all other children structurally).  The left unit stays definitional [eq]. *)
Inductive CmdEq {A : Type} : Cmd A -> Cmd A -> Prop :=
  | CE_ret : forall a, CmdEq (CRet a) (CRet a)
  | CE_out : forall b xs c c', CmdEq c c' -> CmdEq (COut b xs c) (COut b xs c')
  | CE_pan : forall v, CmdEq (CPan v) (CPan v)
  | CE_dfr : forall d c c', CmdEq c c' -> CmdEq (CDfr d c) (CDfr d c')
  | CE_wr  : forall l v c c', CmdEq c c' -> CmdEq (CWrite l v c) (CWrite l v c')
  | CE_rd  : forall l f g, (forall x, CmdEq (f x) (g x)) -> CmdEq (CRead l f) (CRead l g).
Lemma CmdEq_refl : forall {A} (c : Cmd A), CmdEq c c.
Proof.
  intros A c;
    induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH] using Cmd_rect';
    constructor; auto.
Qed.

Lemma cbind_ret_l : forall {A B} (a : A) (k : A -> Cmd B), cbind (CRet a) k = k a.
Proof. reflexivity. Qed.
Lemma cbind_ret_r : forall {A} (c : Cmd A), CmdEq (cbind c (fun a => CRet a)) c.
Proof.
  intros A c;
    induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH] using Cmd_rect';
    cbn [cbind]; constructor; auto.
Qed.
Lemma cbind_assoc : forall {A B C} (c : Cmd A) (k : A -> Cmd B) (h : B -> Cmd C),
  CmdEq (cbind (cbind c k) h) (cbind c (fun a => cbind (k a) h)).
Proof.
  intros A B C c k h.
  induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH] using Cmd_rect';
    cbn [cbind].
  - apply CmdEq_refl.
  - constructor; exact IH.
  - constructor.
  - constructor; exact IH.
  - constructor; exact IH.
  - constructor; intro x; exact (IH x).
Qed.

(** ---- The AUTHORITATIVE (and ONLY) operational interpreter — [defer] is no longer a no-op ----

    [run_cmd] runs the body THEN its defers at function-scope return (LIFO, on panic too).  There is no
    shallow [Cmd -> IO] reading of a [Cmd]: a sequential [World -> Outcome] cannot run a func-scoped defer,
    so a "shallow" reading would DROP the deferred effect — precisely the #12 bug — which is why [run_cmd]
    is the sole semantics (and why [builtins.defer_call] FAILS LOUD instead of silently dropping). *)
Definition oc_world {A} (oc : Outcome A) : World := match oc with ORet _ w => w | OPanic _ w => w end.
Definition oc_set_world {A} (oc : Outcome A) (w : World) : Outcome A :=
  match oc with ORet a _ => ORet a w | OPanic v _ => OPanic v w end.

(** ---- The heap ops' World glue ----
    A heap cell and a boxed value are the SAME data up to pair order ([RefCell] stores
    (tag, value), [GoAny] (value, tag)); a WRITE is tag-PRESERVING (a Go heap cell never
    changes type — [tag_eq] recovers the proof or the write is REJECTED); and an access to
    an UNALLOCATED location has NO behavior at all (Go's safe fragment cannot reach one:
    nil is caught at the POINTER level before a location exists), so [go] makes the whole
    run ABSENT ([None]) — never a default value, never an invented panic. *)
Definition any_of_cell (cell : RefCell) : GoAny :=
  match cell with existT _ T (t, x) => existT _ T (x, t) end.
Definition heap_write (l : nat) (v : GoAny) (w : World) : option World :=
  match w_refs w l, v with
  | Some (existT _ T (tc, _)), existT _ A (x, ta) =>
      match tag_eq ta tc with
      | Some _ => Some (mkWorld (fun k => if Nat.eqb k l
                                          then Some (existT _ A (ta, x))
                                          else w_refs w k)
                                (w_chans w) (w_maps w) (w_next w) (w_output w))
      | None => None
      end
  | None, _ => None
  end.

Lemma heap_write_output : forall l v w w',
  heap_write l v w = Some w' -> w_output w' = w_output w.
Proof.
  intros l v w w' H. unfold heap_write in H.
  destruct (w_refs w l) as [[T [tc y]]|]; [ | discriminate H ].
  destruct v as [A [x ta]].
  destruct (tag_eq ta tc); [ | discriminate H ].
  injection H as <-. reflexivity.
Qed.

(** [go c w] runs [c]'s body, ACCUMULATING the deferred actions (without running them yet).  Structural
    on [c] — the CPS continuations are subterms (a [CRead] continuation's application included), so no
    fuel needed here.  OPTION-VALUED: an unallocated or tag-mismatched heap access has no behavior, so
    the run is ABSENT — [None] here makes [run_cmd] [None] at EVERY fuel. *)
Fixpoint go {A} (c : Cmd A) (w : World) : option (Outcome A * list (Cmd unit)) :=
  match c with
  | CRet a => Some (ORet a w, nil)
  | COut b xs c' => go c' (w_log b xs w)
  | CPan v => Some (OPanic v w, nil)
  | CDfr d c' => match go c' w with
                 | Some (oc, ds) => Some (oc, ds ++ (d :: nil))
                 | None => None
                 end
  | CWrite l v c' => match heap_write l v w with
                     | Some w' => go c' w'
                     | None => None
                     end
  | CRead l f => match w_refs w l with
                 | Some cell => go (f (any_of_cell cell)) w
                 | None => None
                 end
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

    THE DEFECT THIS SHAPE PREVENTS: a runner that STOPPED at the first panicking defer
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
        match go d (oc_world acc) with
        | None => None                                (* an absent deferred body makes the whole run absent *)
        | Some (oc_d, ds_d) =>
            match run_defers n ds_d oc_d with         (* d's net outcome: its body THEN its own nested defers *)
            | None => None
            | Some net_d =>
                let acc' := match net_d with
                            | OPanic v' w' => OPanic v' w'        (* d panicked: REPLACE the active panic *)
                            | ORet _ w'    => oc_set_world acc w' (* d returned: KEEP the active panic, advance world *)
                            end in
                run_defers n ds' acc'                 (* ...then ALWAYS run the older defers *)
            end
        end
    end
  end.

(** Full func-scope run: the body, THEN its defers (LIFO), keeping the body's value or propagating a
    deferred panic.  [defer] is FAITHFUL — a no-op defer would erase the deferred effect. *)
Definition run_cmd (fuel : nat) {A} (c : Cmd A) (w : World) : option (Outcome A) :=
  match go c w with
  | None => None
  | Some (oc, ds) =>
      match run_defers fuel ds (oc_unit oc) with    (* seed the active panic with the body's own outcome *)
      | Some (ORet _ w') => Some (oc_set_world oc w')
      | Some (OPanic v w') => Some (OPanic v w')
      | None => None
      end
  end.

(** [no_defer c] — [c] registers no [CDfr]: a straight-line output/panic/return command.  A pure [Cmd]
    predicate, so it lives here (cmd.v); consumed by GoSemSafe's defer-free exact-output panic lemmas
    ([go_panics_world]/[run_cmd_panics_world]).  The ustep bridge is SEPARATE:
    [cmd_unified.bridge_heap_agrees] covers every COMPLETING [c] (heap, defers, panics). *)
Fixpoint no_defer (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => no_defer c' | CPan _ => true | CDfr _ _ => false
  | CWrite _ _ _ => false | CRead _ _ => false   (* heap ops are OUTSIDE the no_defer fragment this slice
       (a boolean cannot scan under [CRead]'s binder; [CWrite] is excluded with it so the fragment stays
       the straight-line output/panic/return class its consumers were proved on) *)
  end.

(** [cmd_no_panic c] — [c] has NO [CPan] node ANYWHERE (body or any deferred action): it can never end in an
    [OPanic] outcome.  A pure [Cmd] predicate (sibling of [no_defer]), so it lives here in cmd.v — the SINGLE
    authority; consumed by GoSemSafe (the panic-free safety property) and cmd_unified.v ([run_cmd_no_panic_ret] —
    a completing panic-free run returns [ORet]); never a second copy. *)
Fixpoint cmd_no_panic (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => cmd_no_panic c' | CPan _ => false | CDfr d c' => cmd_no_panic d && cmd_no_panic c'
  | CWrite _ _ _ => false | CRead _ _ => false   (* CONSERVATIVE: the decidable panic-free gate also
       promises COMPLETION (the ∃-fuel [ORet] run), which a heap op cannot guarantee (an unallocated or
       tag-mismatched access is ABSENT at every fuel) and a boolean cannot scan under [CRead]'s binder —
       heap programs leave this gate until a finer, allocation-aware analysis exists *)
  end.

(** [no_heap c] — [c] contains NO heap node ([CWrite]/[CRead]) anywhere, body or deferred.  The decidable
    fragment on which the ∃-fuel termination theorem below holds: a heap access can be ABSENT ([go] = [None])
    at EVERY fuel, so unconditional termination is FALSE outside this fragment — completion there is a
    per-program premise, never a theorem.  [cmd_no_panic] is a strict subset (its heap arms are [false] too),
    so panic-free consumers inherit [no_heap] for free ([cmd_no_panic_no_heap] below). *)
Fixpoint no_heap (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => no_heap c'
  | CPan _ => true | CDfr d c' => no_heap d && no_heap c'
  | CWrite _ _ _ => false | CRead _ _ => false
  end.
Lemma cmd_no_panic_no_heap : forall c, cmd_no_panic c = true -> no_heap c = true.
Proof.
  (* [Cmd_rect'] gives no hypothesis for the DEFERRED body, so recurse structurally
     (both [d] and [c'] are direct subterms — the same shape as [cmd_to_ucmd_fragment]) *)
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f]; cbn [cmd_no_panic no_heap]; intro H.
  - reflexivity.
  - exact (IH c' H).
  - discriminate H.
  - destruct (cmd_no_panic d) eqn:Hd; [ | discriminate H ].
    cbn in H. rewrite (IH d Hd). cbn [andb]. exact (IH c' H).
  - discriminate H.
  - discriminate H.
Qed.

(** ---- TERMINATION on the [no_heap] fragment: [run_cmd] never diverges there — enough fuel returns [Some].
    Pure [run_cmd]/[run_defers] properties over cmd.v's own [go], so they live HERE; the measure is a
    structural node-count ([go d] spends [d]'s body nodes, so its accumulated defer forest is strictly
    smaller).  The node-count is a PLACEHOLDER [1] at [CRead] (no syntactic size exists under a binder —
    the continuation branches over every [GoAny]), which is sound because every measure lemma carries the
    [no_heap] premise and a [no_heap] tree never reaches that arm.  [run_cmd_terminates] is a gated public
    surface ([Print Assumptions] below); consumed by cmd_unified.v and GoSem's run layer, whose commands are
    [no_heap] via [cmd_no_panic_no_heap] or by construction. *)
Local Fixpoint cmd_sz (c : Cmd unit) : nat :=
  match c with
  | CRet _ => 1 | COut _ _ c' => S (cmd_sz c') | CPan _ => 1 | CDfr d c' => S (cmd_sz d + cmd_sz c')
  | CWrite _ _ c' => S (cmd_sz c') | CRead _ _ => 1
  end.
Local Fixpoint defers_sz (ds : list (Cmd unit)) : nat :=
  match ds with nil => 0 | d :: ds' => cmd_sz d + defers_sz ds' end.
Local Lemma defers_sz_app : forall ds1 ds2, defers_sz (ds1 ++ ds2) = defers_sz ds1 + defers_sz ds2.
Proof. induction ds1 as [|d ds1 IH]; intro ds2; cbn; [reflexivity | rewrite IH; lia]. Qed.

Fixpoint no_heap_all (ds : list (Cmd unit)) : bool :=
  match ds with nil => true | d :: ds' => no_heap d && no_heap_all ds' end.
Lemma no_heap_all_app : forall ds1 ds2,
  no_heap_all (ds1 ++ ds2) = (no_heap_all ds1 && no_heap_all ds2)%bool.
Proof.
  induction ds1 as [|d ds1 IH]; intro ds2; cbn; [reflexivity | rewrite IH, Bool.andb_assoc; reflexivity].
Qed.

(** On the [no_heap] fragment [go] always SUCCEEDS, its defer forest is [no_heap] too, and that forest is
    strictly SMALLER than [d] (its body nodes are spent) — the three facts the bounded-fuel induction
    threads together. *)
Lemma go_no_heap : forall (d : Cmd unit) w, no_heap d = true ->
  exists oc ds, go d w = Some (oc, ds) /\ no_heap_all ds = true /\ defers_sz ds < cmd_sz d.
Proof.
  intro d; induction d as [a | b xs c' IH | v | d0 c' IH | l v c' IH | l f IH] using Cmd_rect';
    intros w Hnh; cbn [no_heap] in Hnh; cbn [go cmd_sz].
  - exists (ORet a w), nil.
    repeat split; try reflexivity; cbn; lia.
  - destruct (IH (w_log b xs w) Hnh) as [oc [ds [Hgo [Hall Hsz]]]].
    exists oc, ds. repeat split; try exact Hgo; try exact Hall; lia.
  - exists (OPanic v w), nil.
    repeat split; try reflexivity; cbn; lia.
  - destruct (no_heap d0) eqn:Hd0; [ | discriminate Hnh ]. cbn in Hnh.
    destruct (IH w Hnh) as [oc [ds [Hgo [Hall Hsz]]]].
    rewrite Hgo. exists oc, (ds ++ (d0 :: nil)).
    repeat split.
    + rewrite no_heap_all_app. cbn. rewrite Hall, Hd0. reflexivity.
    + rewrite defers_sz_app. cbn [defers_sz]. lia.
  - discriminate Hnh.
  - discriminate Hnh.
Qed.

(** One definitional unfolding of [run_defers] over a [cons] with fuel to spare — a controlled rewrite so
    consumers need not fight [cbn]'s aggressiveness on the (variable-list) tail recursion.  PUBLIC: shared with
    cmd_unified.v's unwind/characterization lemmas. *)
Lemma run_defers_unfold : forall n d ds acc,
  run_defers (S n) (d :: ds) acc
    = match go d (oc_world acc) with
      | None => None
      | Some (oc_d, ds_d) =>
          match run_defers n ds_d oc_d with
          | None => None
          | Some net_d =>
              run_defers n ds (match net_d with
                               | OPanic v' w' => OPanic v' w'
                               | ORet _ w' => oc_set_world acc w' end)
          end
      end.
Proof. reflexivity. Qed.

(** [run_defers] is MONOTONE in fuel: extra fuel never changes a successful result (it only guards against
    exhaustion).  Induction on the fuel [f]. *)
Local Lemma run_defers_mono : forall f ds acc r,
  run_defers f ds acc = Some r -> forall f', f <= f' -> run_defers f' ds acc = Some r.
Proof.
  induction f as [| n IH]; intros ds acc r H f' Hle; [ discriminate H | ].
  destruct f' as [| n']; [ inversion Hle | ]. apply le_S_n in Hle.
  destruct ds as [| d ds']; [ cbn in H |- *; exact H | ].
  rewrite run_defers_unfold in H. rewrite run_defers_unfold.
  destruct (go d (oc_world acc)) as [[oc_d ds_d]|]; [ | discriminate H ].
  destruct (run_defers n ds_d oc_d) as [net_d|] eqn:Enet; [ | discriminate H ].
  rewrite (IH ds_d oc_d net_d Enet n' Hle). exact (IH ds' _ r H n' Hle).
Qed.

(** [run_defers] TERMINATES for enough fuel, over ARBITRARY nesting: bounded strong induction on the defer
    forest's node-count [defers_sz] (each [go d] peels [d] into a strictly-smaller sub-forest — [go_no_heap]),
    lifting the two sub-results to a common fuel via [run_defers_mono].  No well-founded machinery — plain [nat]
    induction on the [defers_sz] bound.  The tail [ds']'s seed depends on the nested run's RESULT, so the two
    sub-runs are resolved to concrete [net_d]/[r] before choosing the common fuel. *)
Local Lemma run_defers_terminates : forall ds acc,
  no_heap_all ds = true -> exists f, run_defers f ds acc <> None.
Proof.
  assert (aux : forall n ds acc, no_heap_all ds = true -> defers_sz ds <= n ->
                exists f, run_defers f ds acc <> None).
  { induction n as [| n IH]; intros ds acc Hnh Hle.
    - destruct ds as [| d ds']; [ exists 1; cbn; discriminate | ].
      cbn [defers_sz] in Hle. cbn in Hnh.
      destruct (no_heap d) eqn:Hd; [ | discriminate Hnh ].
      destruct (go_no_heap d (oc_world acc) Hd) as [oc_d [ds_d [_ [_ Hsz]]]]. lia.
    - destruct ds as [| d ds']; [ exists 1; cbn; discriminate | ].
      cbn [defers_sz] in Hle. cbn in Hnh.
      destruct (no_heap d) eqn:Hd; [ | discriminate Hnh ]. cbn in Hnh.
      destruct (go_no_heap d (oc_world acc) Hd) as [oc_d [ds_d [Hgo [Hall Hsz]]]].
      destruct (IH ds_d oc_d Hall) as [f1 H1]; [ lia | ].
      destruct (run_defers f1 ds_d oc_d) as [net_d|] eqn:Enet; [ | exfalso; apply H1; reflexivity ].
      destruct (IH ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end) Hnh)
        as [f2 H2]; [ lia | ].
      destruct (run_defers f2 ds' (match net_d with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world acc w' end))
        as [r|] eqn:Erest; [ | exfalso; apply H2; reflexivity ].
      exists (S (Nat.max f1 f2)).
      assert (Hfull : run_defers (S (Nat.max f1 f2)) (d :: ds') acc = Some r).
      { rewrite run_defers_unfold, Hgo.
        rewrite (run_defers_mono _ _ _ _ Enet (Nat.max f1 f2) ltac:(lia)). cbn match.
        exact (run_defers_mono _ _ _ _ Erest (Nat.max f1 f2) ltac:(lia)). }
      rewrite Hfull. discriminate. }
  intros ds acc Hnh. exact (aux (defers_sz ds) ds acc Hnh (le_n _)).
Qed.

(** [run_cmd] TERMINATES for enough fuel on the [no_heap] fragment (nested defers included): the body
    ([go], always [Some] there) plus the defer forest ([run_defers_terminates]).  OUTSIDE the fragment the
    ∃-fuel claim is FALSE by design — an absent heap access is [None] at every fuel — so completion is a
    per-program premise there, never a theorem. *)
Theorem run_cmd_terminates : forall (c : Cmd unit) w,
  no_heap c = true -> exists fuel oc, run_cmd fuel c w = Some oc.
Proof.
  intros c w Hnh.
  destruct (go_no_heap c w Hnh) as [oc0 [ds [Hgo [Hall _]]]].
  destruct (run_defers_terminates ds (oc_unit oc0) Hall) as [fuel Hrd].
  destruct (run_defers fuel ds (oc_unit oc0)) as [result|] eqn:Erd;
    [ | exfalso; apply Hrd; reflexivity ].
  exists fuel. unfold run_cmd. rewrite Hgo, Erd.
  destruct result as [[] w' | v w']; eexists; reflexivity.
Qed.
Print Assumptions run_cmd_terminates.

(** ---- The #12 fix, demonstrated ---- *)

(** [defer println(a); defer println(b); return] prints b THEN a (LIFO at return), exactly as Go. *)
Example defer_runs_lifo : forall (a b : GoAny) (w : World),
  run_cmd 5 (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt))) w
    = Some (ORet tt (w_log true (a :: nil) (w_log true (b :: nil) w))).
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
