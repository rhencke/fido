(** Deep-embedded command tree [Cmd] — the operational FOUNDATION (one
    authoritative semantics; defer as a REAL construct).

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
  (* the HEAP pair (appended LAST so existing destruct/induction
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

(** ---- The AUTHORITATIVE (and ONLY) operational interpreter ----

    [run_cmd] runs the body THEN its defers at function-scope return (LIFO, on panic too).  There is no
    shallow [Cmd -> IO] reading of a [Cmd]: a sequential [World -> Outcome] cannot run a func-scoped defer,
    so a "shallow" reading would DROP the deferred effect — which is why [run_cmd]
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
    the run is ABSENT — [None] here makes [run_cmd] [None]. *)
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

(** The TOTAL-per-structure interpreter.  [CDfr d c'] is DEFER-COMPOSITIONAL: run the
    continuation [c'] (whose own later defers unwind inside it), then run [d] as its OWN func scope
    from the resulting world, then COMBINE — a returning defer KEEPS the active outcome (value or
    panic in flight) and advances the world; a panicking defer REPLACES the active panic.  Later
    defers sit deeper in the continuation, so they unwind FIRST — LIFO, as Go — and EVERY defer's
    effects happen (a newer panic merely replaces the active one; older defers still run: a runner
    that stopped at the first panicking defer would permit FALSE heap/output/resource-release
    proofs).  Structural: [d] and [c'] are subterms and [CRead]'s continuation application is
    guard-accepted, so divergence is UNREPRESENTABLE ([Cmd] is a well-founded tree) — the option is
    heap-ABSENCE only (an unallocated or tag-mismatched access has no behavior), never exhaustion. *)
Fixpoint run_cmd {A} (c : Cmd A) (w : World) : option (Outcome A) :=
  match c with
  | CRet a => Some (ORet a w)
  | COut b xs c' => run_cmd c' (w_log b xs w)
  | CPan v => Some (OPanic v w)
  | CDfr d c' =>
      match run_cmd c' w with
      | None => None
      | Some oc =>
          match run_cmd d (oc_world oc) with
          | None => None
          | Some (ORet _ w') => Some (oc_set_world oc w')   (* d returned: keep the active outcome *)
          | Some (OPanic v w') => Some (OPanic v w')        (* d panicked: replace the active panic *)
          end
      end
  | CWrite l v c' =>
      match heap_write l v w with
      | Some w' => run_cmd c' w'
      | None => None
      end
  | CRead l f =>
      match w_refs w l with
      | Some cell => run_cmd (f (any_of_cell cell)) w
      | None => None
      end
  end.

(** ---- The RELATIONAL face of the semantics: [unwind_defers] + [eval_cmd] ----
    [go] is the body relation (as a total function: [go c w = Some (oc, ds)] — the body's outcome
    plus its collected defer forest); [unwind_defers ds acc r] is the LIFO unwind as an INDUCTIVE
    derivation — [UwCons] runs one deferred scope (its body via [go], its own nested forest via a
    SUB-DERIVATION) and threads the active outcome exactly as [run_cmd]'s combine.  Derivations give
    consumers (the ustep bridge) an induction principle whose nested-forest case is a strict
    sub-derivation — the induction the deleted fuel used to fake.  [eval_cmd] packages both; it is
    EQUIVALENT to the structural [run_cmd] ([run_cmd_eval]/[eval_run_cmd] below), so either spelling
    is the same semantic fact and there is ONE authority. *)
Inductive unwind_defers : list (Cmd unit) -> Outcome unit -> Outcome unit -> Prop :=
  | UwNil  : forall acc, unwind_defers nil acc acc
  | UwCons : forall d ds acc oc_d ds_d net r,
      go d (oc_world acc) = Some (oc_d, ds_d) ->
      unwind_defers ds_d (oc_unit oc_d) net ->
      unwind_defers ds (match net with
                        | OPanic v' w' => OPanic v' w'
                        | ORet _ w'    => oc_set_world acc w' end) r ->
      unwind_defers (d :: ds) acc r.

Definition eval_cmd {A} (c : Cmd A) (w : World) (oc : Outcome A) : Prop :=
  exists oc0 ds r,
    go c w = Some (oc0, ds)
    /\ unwind_defers ds (oc_unit oc0) r
    /\ oc = match r with
            | ORet _ w'   => oc_set_world oc0 w'
            | OPanic v w' => OPanic v w'
            end.

(** Unwind derivations COMPOSE and SPLIT over append — the accumulator threads uniformly. *)
Lemma unwind_app : forall ds1 acc mid, unwind_defers ds1 acc mid ->
  forall ds2 r, unwind_defers ds2 mid r -> unwind_defers (ds1 ++ ds2) acc r.
Proof.
  intros ds1 acc mid H1; induction H1 as [acc | d ds acc oc_d ds_d net r' Hgo Hnest IHn Hrest IHr];
    intros ds2 r H2; cbn [app].
  - exact H2.
  - exact (UwCons d (ds ++ ds2) acc oc_d ds_d net r Hgo Hnest (IHr ds2 r H2)).
Qed.
Lemma unwind_split : forall ds1 ds2 acc r, unwind_defers (ds1 ++ ds2) acc r ->
  exists mid, unwind_defers ds1 acc mid /\ unwind_defers ds2 mid r.
Proof.
  induction ds1 as [| d ds1 IH]; intros ds2 acc r H; cbn [app] in H.
  - exists acc. split; [ exact (UwNil acc) | exact H ].
  - inversion H as [| d0 ds0 acc0 oc_d ds_d net r0 Hgo Hnest Hrest Heqd Heqacc Heqr ]; subst.
    destruct (IH ds2 _ r Hrest) as [mid [Hm1 Hm2]].
    exists mid. split; [ exact (UwCons d ds1 acc oc_d ds_d net mid Hgo Hnest Hm1) | exact Hm2 ].
Qed.

(** A panic in flight is NEVER lost: an unwind seeded by a panic ends in a panic (a returning
    defer keeps the seed via [oc_set_world]; a panicking one replaces it with another panic). *)
Lemma unwind_panic_stays : forall ds acc r, unwind_defers ds acc r ->
  forall v w, acc = OPanic v w -> exists v' w', r = OPanic v' w'.
Proof.
  intros ds acc r H; induction H as [acc | d ds acc oc_d ds_d net r Hgo Hnest IHn Hrest IHr];
    intros v w ->.
  - exists v, w. reflexivity.
  - destruct net as [[] wn | vn wn]; cbn [oc_set_world] in IHr.
    + exact (IHr v wn eq_refl).
    + exact (IHr vn wn eq_refl).
Qed.

(** run_cmd ⊆ eval_cmd: the structural interpreter's every completing run has a derivation.
    Structural on [c]; the [CDfr] case splices the continuation's derivation with the deferred
    scope's via [unwind_app]. *)
Theorem run_cmd_eval : forall (c : Cmd unit) w oc,
  run_cmd c w = Some oc -> eval_cmd c w oc.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f] w oc H; cbn [run_cmd] in H.
  - injection H as <-. exists (ORet a w), nil, (ORet tt w).
    split; [ reflexivity | split; [ exact (UwNil _) | reflexivity ] ].
  - destruct (IH c' (w_log b xs w) oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
    exists oc0, ds, r. split; [ cbn [go]; exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - injection H as <-. exists (OPanic v w), nil, (OPanic v w).
    split; [ reflexivity | split; [ exact (UwNil _) | reflexivity ] ].
  - destruct (run_cmd c' w) as [ocm|] eqn:Em; [ | discriminate H ].
    destruct (run_cmd d (oc_world ocm)) as [ocd|] eqn:Ed; [ | discriminate H ].
    destruct (IH c' w ocm Em) as [oc0 [ds0 [r0 [Hgo0 [Hun0 Hocm]]]]].
    destruct (IH d (oc_world ocm) ocd Ed) as [ocd0 [dsd [rd [Hgod [Hund Hocd]]]]].
    (* d's scope as ONE [UwCons] over the tail [nil]; its net [ocd] = the seeded unwind result
       (at unit the seed [oc_unit ocd0] carries the status, so the combine collapses —
       the impossible panic-seed/return-result corner is closed by [unwind_panic_stays]) *)
    assert (Hworld : oc_world ocm = oc_world r0)
      by (subst ocm; destruct r0 as [[] w0 | v0 w0];
          [ destruct oc0; reflexivity | reflexivity ]).
    assert (Hnet : ocd = rd).
    { subst ocd. destruct ocd0 as [[] wd | vd wd]; cbn [oc_unit] in Hund.
      - destruct rd as [[] wr | vr wr]; cbn [oc_set_world]; reflexivity.
      - destruct (unwind_panic_stays dsd (OPanic vd wd) rd Hund vd wd eq_refl) as [v' [w' ->]].
        reflexivity. }
    exists oc0, (ds0 ++ (d :: nil)),
      (match ocd with OPanic v' w' => OPanic v' w' | ORet _ w' => oc_set_world r0 w' end).
    split; [ cbn [go]; rewrite Hgo0; reflexivity | ].
    split.
    + eapply unwind_app; [ exact Hun0 | ].
      eapply (UwCons d nil r0 ocd0 dsd rd).
      * rewrite <- Hworld. exact Hgod.
      * exact Hund.
      * rewrite <- Hnet.
        destruct ocd as [[] wD | vD wD]; cbn [oc_set_world]; exact (UwNil _).
    + subst ocm.
      destruct ocd as [[] wD | vD wD]; cbn.
      * destruct r0 as [[] w0 | v0 w0]; cbn [oc_set_world] in H |- *;
          destruct oc0 as [[] wA | vA wA]; cbn [oc_set_world] in H |- *;
          injection H as <-; reflexivity.
      * injection H as <-. reflexivity.
  - destruct (heap_write l v w) as [w'|] eqn:E; [ | discriminate H ].
    destruct (IH c' w' oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
    exists oc0, ds, r. split; [ cbn [go]; rewrite E; exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - destruct (w_refs w l) as [cell|] eqn:E; [ | discriminate H ].
    destruct (IH (f (any_of_cell cell)) w oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
    exists oc0, ds, r. split; [ cbn [go]; rewrite E; exact Hgo | split; [ exact Hun | exact Hoc ] ].
Qed.

(** eval_cmd ⊆ run_cmd (the converse — together the two directions make [eval_cmd] and [run_cmd]
    the SAME semantic fact, one authority in two spellings).  Structural on [c]; the [CDfr] case
    splits the appended forest ([unwind_split]) and inverts the deferred scope's [UwCons]. *)
Theorem eval_run_cmd : forall (c : Cmd unit) w oc,
  eval_cmd c w oc -> run_cmd c w = Some oc.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f] w oc (oc0 & ds & r & Hgo & Hun & Hoc);
    cbn [go] in Hgo; cbn [run_cmd].
  - injection Hgo as <- <-. inversion Hun; subst. reflexivity.
  - apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - injection Hgo as <- <-. inversion Hun; subst. reflexivity.
  - destruct (go c' w) as [[ocb ds0]|] eqn:Hgo0; [ | discriminate Hgo ].
    injection Hgo as -> <-.
    destruct (unwind_split ds0 (d :: nil) (oc_unit oc0) r Hun) as [mid [Hun0 Hund]].
    rewrite (IH c' w (match mid with ORet _ w' => oc_set_world oc0 w' | OPanic v w' => OPanic v w' end)
               (ex_intro _ oc0 (ex_intro _ ds0 (ex_intro _ mid (conj Hgo0 (conj Hun0 eq_refl)))))).
    cbn beta iota.
    inversion Hund as [| d0 ds' acc0 oc_d ds_d net r' Hgod Hnest Hrest Heqd Heqacc Heqr ]; subst.
    inversion Hrest; subst.
    assert (Hwmid : oc_world (match mid with ORet _ w' => oc_set_world oc0 w'
                              | OPanic v w' => OPanic v w' end) = oc_world mid)
      by (destruct mid as [[] wm | vm wm]; [ destruct oc0; reflexivity | reflexivity ]).
    rewrite Hwmid.
    (* the deferred scope's own run: its eval package is (oc_d, ds_d, net) — the at-unit combine
       collapses to [net] (a panic-seeded unwind cannot return: [unwind_panic_stays]) *)
    assert (Hnetd : run_cmd d (oc_world mid) = Some net).
    { rewrite (IH d (oc_world mid)
                 (match net with ORet _ w' => oc_set_world oc_d w' | OPanic v w' => OPanic v w' end)
                 (ex_intro _ oc_d (ex_intro _ ds_d (ex_intro _ net (conj Hgod (conj Hnest eq_refl)))))).
      destruct oc_d as [[] wd | vd wd]; cbn [oc_unit] in Hnest.
      - destruct net as [[] wn | vn wn]; cbn [oc_set_world]; reflexivity.
      - destruct (unwind_panic_stays ds_d (OPanic vd wd) net Hnest vd wd eq_refl) as [v' [w' ->]].
        reflexivity. }
    rewrite Hnetd. cbn beta iota.
    destruct net as [[] wn | vn wn].
    + (* d returned: the active outcome survives with d's world *)
      destruct mid as [[] wm | vm wm]; cbn [oc_set_world];
        destruct oc0 as [[] wA | vA wA]; cbn [oc_set_world]; reflexivity.
    + reflexivity.
  - destruct (heap_write l v w) as [w'|] eqn:E; [ | discriminate Hgo ].
    apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - destruct (w_refs w l) as [cell|] eqn:E; [ | discriminate Hgo ].
    apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
Qed.
Print Assumptions run_cmd_eval.
Print Assumptions eval_run_cmd.

(** [no_defer c] — [c] registers no [CDfr]: a straight-line output/panic/return command.  A pure [Cmd]
    predicate, so it lives here (cmd.v); consumed by GoSemSafe's defer-free exact-output panic lemmas
    ([run_cmd_panics_world]).  The ustep bridge is SEPARATE:
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
       promises COMPLETION (the [ORet] run), which a heap op cannot guarantee (an unallocated or
       tag-mismatched access is ABSENT) and a boolean cannot scan under [CRead]'s binder —
       heap programs leave this gate until a finer, allocation-aware analysis exists *)
  end.

(** [no_heap c] — [c] contains NO heap node ([CWrite]/[CRead]) anywhere, body or deferred.  The decidable
    fragment on which the totality theorem below holds: a heap access can be ABSENT ([run_cmd] = [None]),
    so unconditional completion is FALSE outside this fragment — completion there is a
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

(** ---- TOTALITY on the [no_heap] fragment: [run_cmd] COMPLETES there, unconditionally — no bound.
    The option is heap-absence only, and a [no_heap] tree never reaches a heap arm, so a
    structural induction produces the outcome directly.  [run_cmd_terminates] is a gated public
    surface ([Print Assumptions] below); consumed by cmd_unified.v and GoSem's run layer, whose
    commands are [no_heap] via [cmd_no_panic_no_heap] or by construction. *)
Theorem run_cmd_terminates : forall (c : Cmd unit) w,
  no_heap c = true -> exists oc, run_cmd c w = Some oc.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f] w Hnh; cbn [no_heap] in Hnh;
    cbn [run_cmd].
  - exists (ORet a w). reflexivity.
  - exact (IH c' (w_log b xs w) Hnh).
  - exists (OPanic v w). reflexivity.
  - destruct (no_heap d) eqn:Hd; [ | discriminate Hnh ]. cbn in Hnh.
    destruct (IH c' w Hnh) as [oc Hoc]. rewrite Hoc.
    destruct (IH d (oc_world oc) Hd) as [ocd Hocd]. rewrite Hocd.
    destruct ocd as [[] w' | vd w']; eexists; reflexivity.
  - discriminate Hnh.
  - discriminate Hnh.
Qed.
Print Assumptions run_cmd_terminates.

(** ---- The #12 fix, demonstrated ---- *)

(** [defer println(a); defer println(b); return] prints b THEN a (LIFO at return), exactly as Go. *)
Example defer_runs_lifo : forall (a b : GoAny) (w : World),
  run_cmd (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (COut true (b :: nil) (CRet tt)) (CRet tt))) w
    = Some (ORet tt (w_log true (a :: nil) (w_log true (b :: nil) w))).
Proof. reflexivity. Qed.

(** Defers run even when the body PANICS (Go semantics): the deferred [println(a)] still happens, then the
    panic propagates. *)
Example defer_runs_on_panic : forall (a v : GoAny) (w : World),
  run_cmd (CDfr (COut true (a :: nil) (CRet tt)) (CPan v) : Cmd unit) w
    = Some (OPanic v (w_log true (a :: nil) w)).
Proof. reflexivity. Qed.

(** DEFER-UNWIND COMPLETION, LOCKED: a NEWER defer panics (runs FIRST in LIFO) — the OLDER deferred [println(a)] STILL
    RUNS (its output [w_log a] appears) and the panic propagates.  The pre-fix interpreter STOPPED at the
    panicking defer and returned [OPanic v w] with NO [w_log a] — a provably-dropped deferred effect. *)
Example defer_older_runs_after_newer_panics : forall (a v : GoAny) (w : World),
  run_cmd (CDfr (COut true (a :: nil) (CRet tt)) (CDfr (CPan v) (CRet tt)) : Cmd unit) w
    = Some (OPanic v (w_log true (a :: nil) w)).
Proof. reflexivity. Qed.

(** Two panicking defers: the LAST to run (the EARLIER-registered [v1], deepest in LIFO) wins, replacing
    the newer [v2] — exactly Go's "a later panic during unwinding replaces the active one". *)
Example defer_last_panic_wins : forall (v1 v2 : GoAny) (w : World),
  run_cmd (CDfr (CPan v1) (CDfr (CPan v2) (CRet tt)) : Cmd unit) w
    = Some (OPanic v1 w).
Proof. reflexivity. Qed.
