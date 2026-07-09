(** ==================================================================================================
    GoEffects — the EFFECT MODEL: [World] (the concrete proof-only state: ref/channel/map heaps,
    fresh-location counter, observable output trace), [Outcome], [IO A := World -> Outcome A],
    [run_io]/[ret]/[bind]/[panic]/[catch], the OBSERVATIONAL equality [io_eq] (an axiom-free
    setoid: pointwise over [run_io]) with its congruence instances, the derived monad/catch laws,
    and the Hoare layer ([hoare], [hoare_no_panic], [hoare_panic_unreachable]).

    ★ THE IO BOUNDARY: [IO] models ONE terminating-or-panicking effect action — never arbitrary
    Go computation.  Loops, recursion, and divergence live in relational/coinductive layers over
    these single actions (GoCFG.v).  ★ NO LEIBNIZ UPGRADE HERE: [run_io_inj] (io_eq ⇒ eq, the one
    funext touch) lives in the proof-only universe (concurrency.v), OUTSIDE the MVP theorem
    surface — everything in this module and the certified path reasons over [io_eq].
    ================================================================================================ *)
Require Import Coq.Classes.Morphisms.   (* Proper / setoid rewriting for [io_eq] *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoPanic.   (* rt_nil_deref for the nil-func invocation panic *)

(** ---- World: a CONCRETE proof-only state record. ----

    [World] is FULLY CONCRETE — no abstract residue.  [w_refs]/[w_chans]/[w_maps]
    are the mutable-cell / channel / map heaps (each a location [int] -> an
    optional typed cell that stores the value WITH its [GoTypeTag], so an accessor
    can coerce it back to its own view's type), and [w_next] is the next fresh
    location.  Every state primitive (ref/channel/map) is a DEFINITION over these
    fields and their laws are THEOREMS.  Extraction erases the whole record. *)
Definition RefCell : Type := { T : Type & (GoTypeTag T * T)%type }.
Definition RefHeap : Type := nat -> option RefCell.
(** A channel cell: the element type [E] with its [GoTypeTag], the FIFO buffer
    (a [list E]), and the closed flag.  The stored [GoTypeTag] lets an accessor
    coerce the buffer back to its own view's element type (they are equal by
    construction; [tag_eq] recovers the proof). *)
(** A channel cell carries its element tag, FIFO buffer, closed flag, and CAPACITY ([option nat]: [None] =
    unbounded, [Some n] = a bounded buffer). *)
Definition ChanCell : Type := { E : Type & (GoTypeTag E * (list E * (bool * option nat)))%type }.
Definition ChanHeap : Type := nat -> option ChanCell.
(** A map cell: the key type [K] + its tag, then existentially the value type [V]
    + its tag, then the contents as a finite-support function [K -> option V].
    Like the channel cell, the stored tags let an accessor coerce back to its own
    [K]/[V] view (equal by construction). *)
(** The leading [nat] is the map's SIZE (number of live keys) — so Go's [len(m)] is faithfully modelled
    ([map_size]), maintained by [map_upd] (+1 on a genuinely new key) and [map_rem] (−1 on a present key).
    It sits OUTSIDE the existT (size is type-independent), so the value accessor [map_get_fn] is unchanged. *)
Definition MapCell : Type :=
  (nat * { K : Type & (GoTypeTag K * { V : Type & (GoTypeTag V * (K -> option V))%type })%type })%type.
Definition MapHeap : Type := nat -> option MapCell.
Record World : Type := mkWorld
  { w_refs : RefHeap ; w_chans : ChanHeap ; w_maps : MapHeap ; w_next : nat
  (* OBSERVABLE OUTPUT TRACE: each [print]/[println] call appends an event
     [(is_println, args)] here, so [run_io]-equality respects stdout.  Model-only:
     print/println lower to native Go, so this field is never extracted. *)
  ; w_output : list (bool * list GoAny) }.


Inductive Outcome (A : Type) : Type :=
  | ORet   : A -> World -> Outcome A
  | OPanic : GoAny -> World -> Outcome A.
Arguments ORet {A} _ _.
Arguments OPanic {A} _ _.

Definition IO (A : Type) : Type := World -> Outcome A.
Definition run_io {A} (m : IO A) (w : World) : Outcome A := m w.
Definition ret {A} (x : A) : IO A := fun w => ORet x w.
Definition bind {A B} (m : IO A) (f : A -> IO B) : IO B :=
  fun w => match m w with ORet a w' => f a w' | OPanic v w' => OPanic v w' end.
(** [panic v] short-circuits; [catch m h] runs [h] only on a panic outcome (Go's
    [defer func(){ if r := recover(); r != nil { h(r) } }()]). *)
Definition panic {A} (v : GoAny) : IO A := fun w => OPanic v w.
Definition catch {A} (m : IO A) (h : GoAny -> IO A) : IO A :=
  fun w => match m w with ORet a w' => ORet a w' | OPanic v w' => h v w' end.


Notation "m >>' k"    := (bind m (fun _ => k)) (at level 50, left associativity).
Notation "x <-' m ;; k" := (bind m (fun x => k))
  (at level 80, m at level 90, right associativity).

(** The [run_*] laws are THEOREMS (by computation). *)
Lemma run_ret : forall {A} (x : A) (w : World),
  run_io (ret x) w = ORet x w.
Proof. reflexivity. Qed.
Lemma run_bind : forall {A B} (m : IO A) (f : A -> IO B) (w : World),
  run_io (bind m f) w =
  match run_io m w with
  | ORet a w'   => run_io (f a) w'
  | OPanic v w' => OPanic v w'        (* panic short-circuits the continuation *)
  end.
Proof. reflexivity. Qed.
Lemma run_panic : forall {A} (v : GoAny) (w : World),
  run_io (@panic A v) w = OPanic v w.
Proof. reflexivity. Qed.
Lemma run_catch : forall {A} (m : IO A) (h : GoAny -> IO A) (w : World),
  run_io (catch m h) w =
  match run_io m w with
  | ORet a w'   => ORet a w'          (* normal: pass through, handler not run *)
  | OPanic v w' => run_io (h v) w'    (* panic: run the handler on the value *)
  end.
Proof. reflexivity. Qed.
(** IO OBSERVATIONAL EQUALITY: two IO actions are equal iff they yield the same
    [Outcome] on every world — the relation the monad/IO laws are stated over.  Every law below
    is AXIOM-FREE: proved POINTWISE, no [run_io_inj]/funext.  Since [run_io m = m], [io_eq] IS
    Go-observable equality of the modeled effects (heap / channel / map / panic / output). *)
Definition io_eq {A} (m m' : IO A) : Prop := forall w, run_io m w = run_io m' w.
Infix "=io=" := io_eq (at level 70, no associativity).

(** [io_eq] is an equivalence and a congruence for [bind]/[catch], so the laws below can be
    setoid-rewritten under those contexts (this is what replaces funext-based [m = m'] reasoning). *)
#[global] Instance io_eq_Equivalence {A} : Equivalence (@io_eq A).
Proof.
  split.
  - intros m w; reflexivity.
  - intros m m' H w; symmetry; apply H.
  - intros m m' m'' H1 H2 w; rewrite H1; apply H2.
Qed.
#[global] Instance bind_Proper {A B} :
  Proper (io_eq ==> pointwise_relation A io_eq ==> io_eq) (@bind A B).
Proof.
  intros m m' Hm f f' Hf w. rewrite !run_bind, (Hm w).
  destruct (run_io m' w) as [a w' | v w'].
  - apply Hf.
  - reflexivity.
Qed.
#[global] Instance catch_Proper {A} :
  Proper (io_eq ==> pointwise_relation GoAny io_eq ==> io_eq) (@catch A).
Proof.
  intros m m' Hm h h' Hh w. rewrite !run_catch, (Hm w).
  destruct (run_io m' w) as [a w' | v w'].
  - reflexivity.
  - apply Hh.
Qed.
(** [run_io] respects [io_eq] — so an [io_eq] fact setoid-rewrites under [run_io _ w]. *)
#[global] Instance run_io_Proper {A} : Proper (io_eq ==> eq ==> eq) (@run_io A).
Proof. intros m m' Hm w w' Hw. subst w'. apply Hm. Qed.


(** ---- Monad laws — provable lemmas, AXIOM-FREE (pointwise over [io_eq], no funext). ---- *)
Lemma bind_ret_l : forall {A B} (x : A) (f : A -> IO B),
  bind (ret x) f =io= f x.
Proof. intros A B x f w. rewrite run_bind, run_ret. reflexivity. Qed.

Lemma bind_ret_r : forall {A} (m : IO A),
  bind m (@ret A) =io= m.
Proof.
  intros A m w. rewrite run_bind. destruct (run_io m w) as [a w' | v w'].
  - rewrite run_ret. reflexivity.
  - reflexivity.
Qed.

Lemma bind_assoc : forall {A B C} (m : IO A) (f : A -> IO B) (g : B -> IO C),
  bind (bind m f) g =io= bind m (fun x => bind (f x) g).
Proof.
  intros A B C m f g w.
  rewrite (run_bind (bind m f) g), (run_bind m f),
          (run_bind m (fun x => bind (f x) g)).
  destruct (run_io m w) as [a w' | v w'].
  - rewrite (run_bind (f a) g). reflexivity.
  - reflexivity.
Qed.

(** [panic] short-circuits any continuation — PROVED from [run_panic]. *)
Lemma bind_panic_l : forall {A B} (x : GoAny) (f : A -> IO B),
  bind (panic x) f =io= panic x.
Proof. intros A B x f w. rewrite run_bind, !run_panic. reflexivity. Qed.

(** [catch] laws — PROVED from [run_catch] (were axioms). *)
Lemma catch_ret : forall {A} (x : A) (h : GoAny -> IO A),
  catch (ret x) h =io= ret x.
Proof. intros A x h w. rewrite run_catch, !run_ret. reflexivity. Qed.

Lemma catch_panic : forall {A} (v : GoAny) (h : GoAny -> IO A),
  catch (panic v) h =io= h v.
Proof. intros A v h w. rewrite run_catch, run_panic. reflexivity. Qed.

(** ---- Hoare logic (PANIC-SENSITIVE) ----
    [{{ P }} m {{ Q }}]: from any [P]-world, [m] runs WITHOUT PANICKING and ends in a
    [Q]-world.  Invariant: a panic maps to [False], NOT [True] — so a valid triple
    GUARANTEES the absence of every modelled panic ([hoare_no_panic]), and [panic] itself
    is specifiable only from a FALSE precondition ([hoare_panic_unreachable] — the
    closed-world "this panic is unreachable" obligation). *)
Definition hoare {A : Type} (P : World -> Prop) (m : IO A)
    (Q : A -> World -> Prop) : Prop :=
  forall w, P w -> match run_io m w with
                   | ORet a w'  => Q a w'
                   | OPanic _ _ => False
                   end.

Notation "{{ P }} m {{ Q }}" :=
  (hoare P m Q)
  (at level 90, m at level 0,
   format "{{ P }} '/  '  m '/  ' {{ Q }}").

Lemma hoare_ret : forall {A} (x : A) (P : World -> Prop),
  {{ P }} ret x {{ fun a w => P w /\ a = x }}.
Proof.
  intros. unfold hoare. intros w Hw.
  rewrite run_ret. split; auto.
Qed.

Lemma hoare_bind : forall {A B} (m : IO A) (f : A -> IO B) P R Q,
  {{ P }} m {{ R }} ->
  (forall a, {{ R a }} f a {{ Q }}) ->
  {{ P }} bind m f {{ Q }}.
Proof.
  intros A B m f P R Q Hm Hf w Hw. unfold hoare in *.
  rewrite run_bind. specialize (Hm w Hw).
  remember (run_io m w) as o eqn:Ho. destruct o as [a w' | v w'].
  - exact (Hf a w' Hm).
  - exact Hm.   (* [m] panicked from a [P]-world: ruled out — [Hm : False] *)
Qed.

Lemma hoare_consequence : forall {A} (m : IO A) P P' Q Q',
  (forall w, P' w -> P w) ->
  {{ P }} m {{ Q }} ->
  (forall a w, Q a w -> Q' a w) ->
  {{ P' }} m {{ Q' }}.
Proof.
  intros A m P P' Q Q' HP H HQ w Hw. unfold hoare in *.
  specialize (H w (HP w Hw)).
  remember (run_io m w) as o eqn:Ho. destruct o as [a w' | v w'].
  - exact (HQ a w' H).
  - exact H.   (* panic ruled out — [H : False] *)
Qed.

(** Sequencing rule for [m >>' n] (run [m], discard its result, run [n]).
    The intermediate assertion [R] holds after [m] and before [n]. *)
Lemma hoare_seq : forall {A B} (m : IO A) (n : IO B) P R Q,
  {{ P }} m {{ fun _ => R }} ->
  {{ R }} n {{ Q }} ->
  {{ P }} (m >>' n) {{ Q }}.
Proof.
  intros A B m n P R Q Hm Hn.
  eapply hoare_bind.
  - exact Hm.
  - intros a. exact Hn.
Qed.

(** [panic] is specifiable ONLY from a FALSE precondition: a triple [{{P}} panic v {{Q}}] forces
    [P] unreachable — the closed-world panic obligation: a raw [panic] in a verified program
    must be proved UNREACHABLE (its precondition refuted). *)
Lemma hoare_panic_unreachable : forall {A} (v : GoAny) (Q : A -> World -> Prop),
  {{ fun _ => False }} @panic A v {{ Q }}.
Proof.
  intros A v Q w HF. destruct HF.
Qed.

(** Panic-FREEDOM is EXPRESSIBLE and DERIVABLE: a valid triple GUARANTEES a NORMAL ([ORet])
    outcome in a [Q]-state.  [{{P}} m {{fun _ _ => True}}] IS "[m] never panics from a
    [P]-world" — the core safety property. *)
Lemma hoare_no_panic : forall {A} (P : World -> Prop) (m : IO A) (Q : A -> World -> Prop),
  {{ P }} m {{ Q }} ->
  forall w, P w -> exists a w', run_io m w = ORet a w' /\ Q a w'.
Proof.
  intros A P m Q H w Hw. specialize (H w Hw).
  destruct (run_io m w) as [a w' | v w'] eqn:E.
  - exists a, w'. split; [reflexivity | exact H].
  - destruct H.
Qed.

(** ==================================================================================================
    OUTPUT + BLOCK-SCOPED DEFER — [print]/[println] as RECORDED effects on the world's [w_output]
    trace (programs that print differently are not [run_io]-equal — [output_distinguishes_programs]),
    and the panic/recover layer's block-scoped [with_defer] (cleanup runs EXACTLY ONCE on both the
    normal and the panic path — proved).  The func-scoped [defer_call] is NOT here: its shallow
    [run_io] meaning is a loud-panic plugin-hook guard, so it lives in GoExtractionHooks.v; the
    faithful func-scoped defer is cmd.v's [CDfr].
    ================================================================================================ *)

(** [print]/[println] write to stdout — a RECORDED effect: each call appends an event
    [(is_println, args)] to the world's [w_output] trace, so programs that print different
    things are not [run_io]-equal.  Lowered BY NAME to native Go [print]/[println]; the
    trace is proof-only and never extracted. *)
Definition w_log (b : bool) (xs : list GoAny) (w : World) : World :=
  mkWorld (w_refs w) (w_chans w) (w_maps w) (w_next w) (w_output w ++ ((b, xs) :: nil)).
Definition print   (xs : list GoAny) : IO unit := fun w => ORet tt (w_log false xs w).
Definition println (xs : list GoAny) : IO unit := fun w => ORet tt (w_log true xs w).

(** The initial world: empty heaps, allocator at 1 — so location 0 is reserved for [nil]. *)
Definition w_init : World := mkWorld (fun _ => None) (fun _ => None) (fun _ => None) 1 nil.

(** [run_io] RESPECTS output — a program that prints TWICE is not provably equal to
    one that prints ONCE.  The result worlds differ in their [w_output] trace length. *)
Example output_distinguishes_programs :
  run_io (bind (println nil) (fun _ => println nil)) w_init
  <> run_io (println nil) w_init.
Proof. vm_compute. discriminate. Qed.

(** [panic], [bind_panic_l], and the PANIC-SENSITIVE Hoare logic ([hoare_panic_unreachable] /
    [hoare_no_panic]) are defined up top with the panic-aware semantics; all are proved lemmas. *)

(** ---- panic / recover semantics ----

    [catch m h] is the semantic of [defer func() { if r := recover(); r != nil { h(r) } }()].
    [recover()] in Go is just the panic value bound by [h] — it needs no separate axiom.

    Compound panics: if [h] itself panics with [w], [catch (panic v) h = h v = panic w],
    so the new panic [w] replaces [v].  This is correct Go semantics and falls out from
    [catch_panic] alone — no extra law needed.

    [with_defer] models [defer cleanup()] (without recover): runs [cleanup] on both
    normal exit and panic exit.  If [cleanup] panics mid-panic, the new panic wins —
    also correct Go semantics, again from [catch_panic] + [bind_panic_l]. *)

(** [catch] is declared up top; [catch_ret] and [catch_panic] are proved
    lemmas (from [run_catch]), not axioms. *)

(** [with_defer cleanup m]: run [m], then run [cleanup] EXACTLY ONCE regardless
    of outcome (Go runs one deferred call once).  If [cleanup] panics, its panic
    replaces any in-flight panic.
    Invariant: cleanup does NOT live inside the [catch] that distinguishes the
    body outcome — [m]'s outcome is reified into a [GoAny + A] sum WITHOUT running
    cleanup, then cleanup runs exactly once on the single post-[catch] path and
    the captured body panic is re-raised. *)
Definition with_defer {A : Type} (cleanup : IO unit) (m : IO A) : IO A :=
  r <-' catch (x <-' m ;; ret (@inr GoAny A x)) (fun v => ret (@inl GoAny A v)) ;;
  cleanup >>' match r with
              | inl v => panic v
              | inr x => ret x
              end.

(** When the guarded body panics, the deferred [cleanup] still runs and the
    original panic propagates afterwards.  Follows from [bind_panic_l] (panic
    short-circuits the body, reifying nothing) and [catch_panic] (the handler
    captures the panic as [inl v]); cleanup then runs once and re-raises it. *)
Lemma with_defer_panic : forall {A} (cleanup : IO unit) (v : GoAny),
  @with_defer A cleanup (panic v) =io= cleanup >>' panic v.
Proof.
  intros A cleanup v. unfold with_defer.
  rewrite bind_panic_l, catch_panic, bind_ret_l. reflexivity.
Qed.

(** Companion lemma for the NORMAL path: when the body returns [x], cleanup runs
    and [x] propagates.  Crucially this holds UNCONDITIONALLY in [cleanup] — even
    a [cleanup] that panics is run exactly once (the RHS mentions [cleanup] once);
    together with [with_defer_panic] it certifies a single cleanup execution on
    both exits. *)
Lemma with_defer_ret : forall {A} (cleanup : IO unit) (x : A),
  @with_defer A cleanup (ret x) =io= cleanup >>' ret x.
Proof.
  intros A cleanup x. unfold with_defer.
  rewrite bind_ret_l, catch_ret, bind_ret_l. reflexivity.
Qed.

(** ---- Integer [range] (Go 1.22, spec "For statements: For range" over an integer): [for i := range n] ----
    Produces [i = 0, 1, …, n-1] (and runs zero times when [n = 0], exactly Go's rule).
    The bound [n] is the iteration COUNT (a [nat] — non-negative, and the structurally
    DECREASING argument, so termination is by construction with no carrier conversion); the produced index
    [i] is the Go [int] index type (the [Z]-carried [GoInt]).  Recognized by name + decl suppressed, so the
    lowering is the native [for i := range n] (the [nat] count renders as the bound). *)
Fixpoint int_range_aux (i : GoInt) (n : nat) (body : GoInt -> IO unit) : IO unit :=
  match n with
  | O    => ret tt
  | S f  => bind (body i) (fun _ => int_range_aux (int_add i (intwrap 1)) f body)
  end.
Definition int_range (n : nat) (body : GoInt -> IO unit) : IO unit :=
  int_range_aux (intwrap 0) n body.

(** Function VALUES.  [gofunc_of] wraps a real closure as a non-nil [GoFunc]; the
    [zero_val (TArrow ..) = None] nil func is the ONLY other inhabitant.  [gofunc_call] is the
    EFFECTFUL invocation: a real closure runs, but a [nil] ([None]) func PANICS with Go's exact
    nil-dereference message ([rt_nil_deref]).  So a nil func is never a silently-callable
    placeholder — extraction emits the bare Go call [f(x)], whose runtime nil-panic MATCHES. *)
Definition gofunc_of {A B} (f : A -> B) : GoFunc A B := SomeFunc f.
Definition gofunc_call {A B} (f : GoFunc A B) (x : A) : IO B :=
  match f with
  | SomeFunc g => ret (g x)
  | NilFunc    => panic rt_nil_deref
  end.
Lemma gofunc_call_of : forall {A B} (f : A -> B) (x : A) (w : World),
  run_io (gofunc_call (gofunc_of f) x) w = ORet (f x) w.
Proof. reflexivity. Qed.
Lemma gofunc_call_nil : forall {A B} (x : A) (w : World),
  run_io (gofunc_call (@NilFunc A B) x) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.
