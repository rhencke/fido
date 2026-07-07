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

    THIS FILE: the syntax for output/panic/defer + the typed HEAP trio ([CWrite]/[CRead]/[CAlloc] — tag-preserving
    writes, ABSENT on unallocated access), [cbind] + the monad laws (over [CmdEq]), and the
    AUTHORITATIVE operational interpreter [run_cmd] — which runs the body THEN its [defer] stack (LIFO,
    func-scope return, on panic too; the #12 fix).  There is NO shallow [Cmd -> IO] reading: a sequential
    [World -> Outcome] cannot run a func-scoped defer at return, so [run_cmd] is the ONLY semantics for a
    [Cmd] (a shallow drop/no-op would silently erase a deferred effect).  The CHANNEL trio
    ([CChSend]/[CChRecv]/[CChClose]) is part of this syntax — the single-goroutine
    deterministic fragment; [catch] and spawn/select are future slices
    (plans/bridge-effects.md). *)
From Fido Require Import preamble.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.   (* the channel trio's Go-faithful panics (send/close on a closed channel) *)
From Fido Require Import GoSlice.
From Stdlib Require Import List Lia.
Import ListNotations.

(** The program syntax.  [COut] = a [print]/[println] of [xs] THEN the continuation; [CPan] = panic
    (no continuation — it short-circuits); [CDfr] = defer; [CWrite]/[CRead]/[CAlloc] = the typed heap trio;
    [CChSend]/[CChRecv]/[CChClose] = the channel trio (single-goroutine deterministic fragment).
    [catch] and spawn/select follow in later slices. *)
Inductive Cmd (A : Type) : Type :=
  | CRet : A -> Cmd A
  | COut : bool -> list GoAny -> Cmd A -> Cmd A
  | CPan : GoAny -> Cmd A
  | CDfr : Cmd unit -> Cmd A -> Cmd A    (* [defer d]; [d] runs at function-scope return *)
  (* the HEAP nodes (appended LAST so existing destruct/induction
     bullet lists keep their order).  [CRead] is the syntax's first value-BINDING
     constructor — its continuation is a function, which shapes everything below:
     structural booleans cannot scan under it, and extensional facts about it need
     [CmdEq], never an axiom. *)
  | CWrite : nat -> GoAny -> Cmd A -> Cmd A   (* *l = v; then k — tag-PRESERVING (typed cell) *)
  | CRead  : nat -> (GoAny -> Cmd A) -> Cmd A   (* x := *l; then k x *)
  (* [CAlloc] (appended LAST, same discipline as the read/write pair): l := new(v); then k l.
     DETERMINISTIC allocator — allocates at EXACTLY [w_next w] and bumps; an any-fresh-l
     rule would be an observably nondeterministic allocator (the continuation branches on
     [l]) and could clobber a mirrored-but-untraced cell.  Freshness ("the cell was [None]",
     "l <> 0") is a THEOREM only under [GoHeap.ValidWorld] — never a totality fact here. *)
  | CAlloc : GoAny -> (nat -> Cmd A) -> Cmd A
  (* the CHANNEL trio (single-goroutine deterministic fragment).  [CChRecv] carries the
     element TAG — GoChan's own [recv] op takes it, so the syntax carrying it is faithful —
     and a closed, drained recv binds the TYPED zero [anyt tag (zero_val tag)].  Would-block
     shapes (send with no room incl. unbuffered, recv on open-empty, any op on an absent
     cell) have NO behavior here ([run_cmd] = [None]): the Cmd layer HAS a stuck outcome,
     unlike the shallow IO ops (whose loud would-block panics are documented stand-ins), so
     absence is the deterministic-fragment gate.  Send/close on closed PANIC as Go does. *)
  | CChSend  : nat -> GoAny -> Cmd A -> Cmd A
  | CChRecv  : nat -> {T : Type & GoTypeTag T} -> (GoAny -> Cmd A) -> Cmd A
  | CChClose : nat -> Cmd A -> Cmd A.
Arguments CRet {A} _.
Arguments COut {A} _ _ _.
Arguments CPan {A} _.
Arguments CDfr {A} _ _.
Arguments CWrite {A} _ _ _.
Arguments CRead {A} _ _.
Arguments CAlloc {A} _ _.
Arguments CChSend {A} _ _ _.
Arguments CChRecv {A} _ _ _.
Arguments CChClose {A} _ _.

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
  (fal : forall v f, (forall l, P (f l)) -> P (CAlloc v f))
  (fsn : forall c v c', P c' -> P (CChSend c v c'))
  (frc : forall c tg f, (forall x, P (f x)) -> P (CChRecv c tg f))
  (fcl : forall c c', P c' -> P (CChClose c c'))
  (c : Cmd A) : P c :=
  match c with
  | CRet a => fret a
  | COut b xs c' => fout b xs c' (Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl c')
  | CPan v => fpan v
  | CDfr d c' => fdfr d c' (Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl c')
  | CWrite l v c' => fwr l v c' (Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl c')
  | CRead l f => frd l f (fun x => Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl (f x))
  | CAlloc v f => fal v f (fun l => Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl (f l))
  | CChSend c v c' => fsn c v c' (Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl c')
  | CChRecv c tg f => frc c tg f (fun x => Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl (f x))
  | CChClose c c' => fcl c c' (Cmd_rect' A P fret fout fpan fdfr fwr frd fal fsn frc fcl c')
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
  | CAlloc v f => CAlloc v (fun l => cbind (f l) k)
  | CChSend c v c' => CChSend c v (cbind c' k)
  | CChRecv c tg f => CChRecv c tg (fun x => cbind (f x) k)
  | CChClose c c' => CChClose c (cbind c' k)
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
  | CE_rd  : forall l f g, (forall x, CmdEq (f x) (g x)) -> CmdEq (CRead l f) (CRead l g)
  | CE_al  : forall v f g, (forall l, CmdEq (f l) (g l)) -> CmdEq (CAlloc v f) (CAlloc v g)
  | CE_sn  : forall c v k k', CmdEq k k' -> CmdEq (CChSend c v k) (CChSend c v k')
  | CE_rc  : forall c tg f g, (forall x, CmdEq (f x) (g x)) -> CmdEq (CChRecv c tg f) (CChRecv c tg g)
  | CE_cl  : forall c k k', CmdEq k k' -> CmdEq (CChClose c k) (CChClose c k').
Lemma CmdEq_refl : forall {A} (c : Cmd A), CmdEq c c.
Proof.
  intros A c;
    induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH | v f IH | ch v c' IH | ch tg f IH | ch c' IH] using Cmd_rect';
    constructor; auto.
Qed.

Lemma cbind_ret_l : forall {A B} (a : A) (k : A -> Cmd B), cbind (CRet a) k = k a.
Proof. reflexivity. Qed.
Lemma cbind_ret_r : forall {A} (c : Cmd A), CmdEq (cbind c (fun a => CRet a)) c.
Proof.
  intros A c;
    induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH | v f IH | ch v c' IH | ch tg f IH | ch c' IH] using Cmd_rect';
    cbn [cbind]; constructor; auto.
Qed.
Lemma cbind_assoc : forall {A B C} (c : Cmd A) (k : A -> Cmd B) (h : B -> Cmd C),
  CmdEq (cbind (cbind c k) h) (cbind c (fun a => cbind (k a) h)).
Proof.
  intros A B C c k h.
  induction c as [a | b xs c' IH | v | d c' IH | l v c' IH | l f IH | v f IH | ch v c' IH | ch tg f IH | ch c' IH] using Cmd_rect';
    cbn [cbind].
  - apply CmdEq_refl.
  - constructor; exact IH.
  - constructor.
  - constructor; exact IH.
  - constructor; exact IH.
  - constructor; intro x; exact (IH x).
  - constructor; intro l; exact (IH l).
  - constructor; exact IH.
  - constructor; intro x; exact (IH x).
  - constructor; exact IH.
Qed.

(** ---- The AUTHORITATIVE (and ONLY) operational interpreter ----

    [run_cmd] runs the body THEN its defers at function-scope return (LIFO, on panic too).  There is no
    shallow [Cmd -> IO] reading of a [Cmd]: a sequential [World -> Outcome] cannot run a func-scoped defer,
    so a "shallow" reading would DROP the deferred effect — which is why [run_cmd]
    is the sole semantics (and why [GoExtractionHooks.defer_call] FAILS LOUD instead of silently dropping). *)
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

Lemma heap_write_next : forall l v w w',
  heap_write l v w = Some w' -> w_next w' = w_next w.
Proof.
  intros l v w w' H. unfold heap_write in H.
  destruct (w_refs w l) as [[T [tc y]]|]; [ | discriminate H ].
  destruct v as [A [x ta]].
  destruct (tag_eq ta tc); [ | discriminate H ].
  injection H as <-. reflexivity.
Qed.

Lemma heap_write_output : forall l v w w',
  heap_write l v w = Some w' -> w_output w' = w_output w.
Proof.
  intros l v w w' H. unfold heap_write in H.
  destruct (w_refs w l) as [[T [tc y]]|]; [ | discriminate H ].
  destruct v as [A [x ta]].
  destruct (tag_eq ta tc); [ | discriminate H ].
  injection H as <-. reflexivity.
Qed.

(** [cell_of_any] is [any_of_cell]'s inverse (pair order); [alloc_world v w] installs
    [v]'s cell at EXACTLY [w_next w] and bumps the allocator — the deterministic allocation
    both [go]/[run_cmd] (below) and the unified mirror perform.  TOTAL: unlike the heap
    pair, allocation cannot be absent. *)
Definition cell_of_any (v : GoAny) : RefCell :=
  match v with existT _ T (x, t) => existT _ T (t, x) end.
Definition alloc_world (v : GoAny) (w : World) : World :=
  mkWorld (fun k => if Nat.eqb k (w_next w) then Some (cell_of_any v) else w_refs w k)
          (w_chans w) (w_maps w) (S (w_next w)) (w_output w).
Lemma alloc_world_output : forall v w, w_output (alloc_world v w) = w_output w.
Proof. reflexivity. Qed.
Lemma any_cell_roundtrip : forall v, any_of_cell (cell_of_any v) = v.
Proof. intros [T [x t]]. reflexivity. Qed.

(** ---- The channel trio's World glue: read/update a channel CELL at a raw location.
    The transitions mirror GoChan's op semantics (closed-send/close panics, buffer FIFO,
    the closed-drained TYPED zero); the would-block shapes are ABSENT in [run_cmd]
    ([None]) rather than the shallow IO ops' loud stand-in panics — the Cmd layer has a
    real stuck outcome, so absence IS the deterministic-fragment gate. *)
Definition chan_cell_upd (c : nat) (cell : ChanCell) (w : World) : World :=
  mkWorld (w_refs w) (fun k => if Nat.eqb k c then Some cell else w_chans w k)
          (w_maps w) (w_next w) (w_output w).
Definition chan_room_cap (buflen : nat) (cap : option nat) : bool :=
  match cap with None => true | Some n => Nat.ltb buflen n end.
Lemma chan_cell_upd_output : forall c cell w, w_output (chan_cell_upd c cell w) = w_output w.
Proof. reflexivity. Qed.
Lemma chan_cell_upd_next : forall c cell w, w_next (chan_cell_upd c cell w) = w_next w.
Proof. reflexivity. Qed.

(** [go c w] runs [c]'s body, ACCUMULATING the deferred actions (without running them yet).  Structural
    on [c] — the CPS continuations are subterms (a [CRead] continuation's application included).
    OPTION-VALUED: an unallocated or tag-mismatched heap access has no behavior, so
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
  | CAlloc v f => go (f (w_next w)) (alloc_world v w)
  | CChSend c v k =>
      match w_chans w c with
      | None => None
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          if closed then Some (OPanic rt_send_closed w, nil)
          else match v with existT _ A0 (x, ta) =>
            match tag_coerce tag ta x with
            | None => None
            | Some xe =>
                if chan_room_cap (length buf) cap
                then go k (chan_cell_upd c (existT _ E (tag, (buf ++ xe :: nil, (closed, cap)))) w)
                else None
            end end
      end
  | CChRecv c tg f =>
      match w_chans w c with
      | None => None
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          match tg with existT _ T tgt =>
            match tag_eq tgt tag with
            | None => None
            | Some _ =>
                match buf with
                | v0 :: rest =>
                    go (f (existT _ E (v0, tag)))
                       (chan_cell_upd c (existT _ E (tag, (rest, (closed, cap)))) w)
                | nil => if closed then go (f (anyt tgt (zero_val tgt))) w else None
                end
            end end
      end
  | CChClose c k =>
      match w_chans w c with
      (* an ABSENT cell is ABSENT, exactly like send/recv on nil: the closed world never
         reaches a nil close ([GoChan]'s [rt_close_nil] guard is the IO layer's open-world
         boundary), and a fragment panic here would have no unified counterpart. *)
      | None => None
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          if closed then Some (OPanic rt_close_closed w, nil)
          else go k (chan_cell_upd c (existT _ E (tag, (buf, (true, cap)))) w)
      end
  end.

(** Project an [Outcome A] to [Outcome unit], keeping its panic value and world — the "active panic"
    carrier threaded through defer unwinding. *)
Definition oc_unit {A} (oc : Outcome A) : Outcome unit :=
  match oc with ORet _ w => ORet tt w | OPanic v w => OPanic v w end.
Lemma oc_unit_world : forall {A} (oc : Outcome A), oc_world (oc_unit oc) = oc_world oc.
Proof. intros A [a w | v w]; reflexivity. Qed.

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
  | CAlloc v f => run_cmd (f (w_next w)) (alloc_world v w)
  | CChSend c v k =>
      match w_chans w c with
      | None => None
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          if closed then Some (OPanic rt_send_closed w)
          else match v with existT _ A0 (x, ta) =>
            match tag_coerce tag ta x with
            | None => None
            | Some xe =>
                if chan_room_cap (length buf) cap
                then run_cmd k (chan_cell_upd c (existT _ E (tag, (buf ++ xe :: nil, (closed, cap)))) w)
                else None
            end end
      end
  | CChRecv c tg f =>
      match w_chans w c with
      | None => None
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          match tg with existT _ T tgt =>
            match tag_eq tgt tag with
            | None => None
            | Some _ =>
                match buf with
                | v0 :: rest =>
                    run_cmd (f (existT _ E (v0, tag)))
                            (chan_cell_upd c (existT _ E (tag, (rest, (closed, cap)))) w)
                | nil => if closed then run_cmd (f (anyt tgt (zero_val tgt))) w else None
                end
            end end
      end
  | CChClose c k =>
      match w_chans w c with
      | None => None   (* absent = absent — see [go]'s arm *)
      | Some (existT _ E (tag, (buf, (closed, cap)))) =>
          if closed then Some (OPanic rt_close_closed w)
          else run_cmd k (chan_cell_upd c (existT _ E (tag, (buf, (true, cap)))) w)
      end
  end.

(** ---- The RELATIONAL face of the semantics: [unwind_defers] + [eval_cmd] ----
    [go] is the body relation (as a total function: [go c w = Some (oc, ds)] — the body's outcome
    plus its collected defer forest); [unwind_defers ds acc r] is the LIFO unwind as an INDUCTIVE
    derivation — [UwCons] runs one deferred scope (its body via [go], its own nested forest via a
    SUB-DERIVATION) and threads the active outcome exactly as [run_cmd]'s combine.  Derivations give
    consumers (the ustep bridge) an induction principle whose nested-forest case is a strict
    sub-derivation.  [eval_cmd] packages both; it is
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
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c'] w oc H; cbn [run_cmd] in H.
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
  - destruct (IH (f (w_next w)) (alloc_world v w) oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
    exists oc0, ds, r. split; [ cbn [go]; exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - (* CChSend *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate H ].
    destruct closed.
    + injection H as <-. exists (OPanic rt_send_closed w), nil, (OPanic rt_send_closed w).
      split; [ cbn [go]; rewrite Ec; reflexivity | split; [ exact (UwNil _) | reflexivity ] ].
    + destruct v as [A0 [x ta]].
      destruct (tag_coerce tag ta x) as [xe|] eqn:Etc; [ | discriminate H ].
      destruct (chan_room_cap (length buf) cap) eqn:Er; [ | discriminate H ].
      destruct (IH c' _ oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
      exists oc0, ds, r.
      split; [ cbn [go]; rewrite Ec; cbn beta iota; rewrite Etc; cbn beta iota; rewrite Er; exact Hgo
             | split; [ exact Hun | exact Hoc ] ].
  - (* CChRecv *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate H ].
    destruct tg as [T tgt].
    destruct (tag_eq tgt tag) as [pf|] eqn:Ete; [ | discriminate H ].
    destruct buf as [|v0 rest].
    + destruct closed; [ | discriminate H ].
      destruct (IH (f (anyt tgt (zero_val tgt))) w oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
      exists oc0, ds, r.
      split; [ cbn [go]; rewrite Ec; cbn beta iota; rewrite Ete; exact Hgo
             | split; [ exact Hun | exact Hoc ] ].
    + destruct (IH (f (existT _ E (v0, tag))) _ oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
      exists oc0, ds, r.
      split; [ cbn [go]; rewrite Ec; cbn beta iota; rewrite Ete; exact Hgo
             | split; [ exact Hun | exact Hoc ] ].
  - (* CChClose *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate H ].
    destruct closed.
    + injection H as <-. exists (OPanic rt_close_closed w), nil, (OPanic rt_close_closed w).
      split; [ cbn [go]; rewrite Ec; reflexivity | split; [ exact (UwNil _) | reflexivity ] ].
    + destruct (IH c' _ oc H) as [oc0 [ds [r [Hgo [Hun Hoc]]]]].
      exists oc0, ds, r.
      split; [ cbn [go]; rewrite Ec; exact Hgo | split; [ exact Hun | exact Hoc ] ].
Qed.

(** eval_cmd ⊆ run_cmd (the converse — together the two directions make [eval_cmd] and [run_cmd]
    the SAME semantic fact, one authority in two spellings).  Structural on [c]; the [CDfr] case
    splits the appended forest ([unwind_split]) and inverts the deferred scope's [UwCons]. *)
Theorem eval_run_cmd : forall (c : Cmd unit) w oc,
  eval_cmd c w oc -> run_cmd c w = Some oc.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c'] w oc (oc0 & ds & r & Hgo & Hun & Hoc);
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
  - apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - (* CChSend *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct closed.
    + injection Hgo as <- <-. inversion Hun; subst. reflexivity.
    + destruct v as [A0 [x ta]].
      destruct (tag_coerce tag ta x) as [xe|] eqn:Etc; [ | discriminate Hgo ].
      destruct (chan_room_cap (length buf) cap) eqn:Er; [ | discriminate Hgo ].
      apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - (* CChRecv *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct tg as [T tgt].
    destruct (tag_eq tgt tag) as [pf|] eqn:Ete; [ | discriminate Hgo ].
    destruct buf as [|v0 rest].
    + destruct closed; [ | discriminate Hgo ].
      apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
    + apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
  - (* CChClose *)
    destruct (w_chans w ch) as [[E [tag [buf [closed cap]]]]|] eqn:Ec; [ | discriminate Hgo ].
    destruct closed.
    + injection Hgo as <- <-. inversion Hun; subst. reflexivity.
    + apply IH. exists oc0, ds, r. split; [ exact Hgo | split; [ exact Hun | exact Hoc ] ].
Qed.


(** [no_defer c] — [c] registers no [CDfr]: a straight-line output/panic/return command.  A pure [Cmd]
    predicate, so it lives here (cmd.v); consumed by GoSemSafe's defer-free exact-output panic lemmas
    ([run_cmd_panics_world]).  The ustep bridge is SEPARATE:
    [cmd_unified.bridge_effects_agree] covers every COMPLETING [c] (heap, allocation, the
    channel trio — buffers/closedness included — defers, panics). *)
Fixpoint no_defer (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => no_defer c' | CPan _ => true | CDfr _ _ => false
  | CWrite _ _ _ => false | CRead _ _ => false | CAlloc _ _ => false
  | CChSend _ _ _ => false | CChRecv _ _ _ => false | CChClose _ _ => false   (* heap/channel ops are OUTSIDE the no_defer fragment this slice
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
  | CWrite _ _ _ => false | CRead _ _ => false | CAlloc _ _ => false
  | CChSend _ _ _ => false | CChRecv _ _ _ => false | CChClose _ _ => false   (* CONSERVATIVE: the decidable panic-free gate also
       promises COMPLETION (the [ORet] run), which a heap op cannot guarantee (an unallocated or
       tag-mismatched access is ABSENT) and a boolean cannot scan under [CRead]'s binder —
       heap programs leave this gate until a finer, allocation-aware analysis exists *)
  end.

(** [structurally_total_cmd c] — [c] contains NO heap node ([CWrite]/[CRead]/[CAlloc]) and NO channel node
    ([CChSend]/[CChRecv]/[CChClose]) anywhere, body or deferred.  The decidable
    fragment on which the totality theorem below holds: a heap access can be ABSENT ([run_cmd] = [None])
    and a channel op can be absent too (would-block / absent cell / tag mismatch),
    so unconditional completion is FALSE outside this fragment — completion there is a
    per-program premise, never a theorem.  [cmd_no_panic] is a strict subset (its heap arms are [false] too),
    so panic-free consumers inherit [structurally_total_cmd] for free ([cmd_no_panic_structurally_total] below). *)
Fixpoint structurally_total_cmd (c : Cmd unit) : bool :=
  match c with
  | CRet _ => true | COut _ _ c' => structurally_total_cmd c'
  | CPan _ => true | CDfr d c' => structurally_total_cmd d && structurally_total_cmd c'
  | CWrite _ _ _ => false | CRead _ _ => false | CAlloc _ _ => false
  | CChSend _ _ _ => false | CChRecv _ _ _ => false | CChClose _ _ => false
  end.
Lemma cmd_no_panic_structurally_total : forall c, cmd_no_panic c = true -> structurally_total_cmd c = true.
Proof.
  (* [Cmd_rect'] gives no hypothesis for the DEFERRED body, so recurse structurally
     (both [d] and [c'] are direct subterms — the same shape as [cmd_to_ucmd_fragment]) *)
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c']; cbn [cmd_no_panic structurally_total_cmd]; intro H.
  - reflexivity.
  - exact (IH c' H).
  - discriminate H.
  - destruct (cmd_no_panic d) eqn:Hd; [ | discriminate H ].
    cbn in H. rewrite (IH d Hd). cbn [andb]. exact (IH c' H).
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate H.
Qed.

(** ---- TOTALITY on the [structurally_total_cmd] fragment: [run_cmd] COMPLETES there, unconditionally — no bound.
    The option is heap/channel-absence only, and a [structurally_total_cmd] tree never reaches a heap or
    channel arm, so a structural induction produces the outcome directly.  [run_cmd_terminates] is a gated public
    surface ([Print Assumptions] below); consumed by cmd_unified.v and GoSem's run layer, whose
    commands are [structurally_total_cmd] via [cmd_no_panic_structurally_total] or by construction. *)
Theorem run_cmd_terminates : forall (c : Cmd unit) w,
  structurally_total_cmd c = true -> exists oc, run_cmd c w = Some oc.
Proof.
  fix IH 1. intros [a | b xs c' | v | d c' | l v c' | l f | v f | ch v c' | ch tg f | ch c'] w Hnh; cbn [structurally_total_cmd] in Hnh;
    cbn [run_cmd].
  - exists (ORet a w). reflexivity.
  - exact (IH c' (w_log b xs w) Hnh).
  - exists (OPanic v w). reflexivity.
  - destruct (structurally_total_cmd d) eqn:Hd; [ | discriminate Hnh ]. cbn in Hnh.
    destruct (IH c' w Hnh) as [oc Hoc]. rewrite Hoc.
    destruct (IH d (oc_world oc) Hd) as [ocd Hocd]. rewrite Hocd.
    destruct ocd as [[] w' | vd w']; eexists; reflexivity.
  - discriminate Hnh.
  - discriminate Hnh.
  - discriminate Hnh.
  - discriminate Hnh.
  - discriminate Hnh.
  - discriminate Hnh.
Qed.
(** The ONE manifest surface for the command semantics: totality on the decidable fragment +
    the run/derivation equivalence, both directions.  Named in PROGRESS.md "Current gates". *)
Definition cmd_semantics_surface := (run_cmd_terminates, run_cmd_eval, eval_run_cmd).
Print Assumptions cmd_semantics_surface.

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
