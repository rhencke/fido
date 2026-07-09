(** ==================================================================================================
    GoChan — Go's [chan T] over the world's channel heap, WITH its whole proof story: the
    ops ([make_chan]/[make_chan_buf]/send/recv/comma-ok recv/close/cap), the derived channel
    laws, the happens-before partial order on channel events (go.dev/ref/mem), the data-race
    definition and the synchronisation theorems, program-level race freedom, the 4th go-mem
    close⤳zero rule, and the goroutine fork edge.  ONE module owns the channel story — the
    model-side concurrency theory lives here, the rstep calculus universe stays in
    concurrency.v.
    ================================================================================================ *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.

(** ---- GoChan ----

    [GoChan A] models Go's [chan T].  [make_chan] allocates an unbuffered
    channel — send blocks until a receiver is ready, so an unbuffered channel
    requires a complementary goroutine.  [make_chan_buf n] allocates a buffered
    channel with capacity [n]; send does not block until the buffer is full,
    making single-goroutine use safe when n > 0. *)

(** The channel allocators are DEFINITIONS: a [GoChan] is a concrete location
    handle, minted from a fresh [w_next] location, and the new
    channel's cell is INITIALISED in [w_chans] (empty buffer, not closed, tagged
    with the element type [tag]).  Lowered by name to [make(chan T)] /
    [make(chan T, n)]; the world-threading body is proof-only. *)
(** The channel cell carries a CAPACITY ([option nat]: [None] = unbounded, [Some n] = a buffer that
    holds at most [n]).  [make_chan] is UNBUFFERED, [Some 0] — an IO send to it finds no room and
    FAILS LOUD (Go BLOCKS pending a receiver; the sequential IO model has no rendezvous).
    [make_chan_buf n] is [Some n]; [send] (below) is capacity-aware. *)
Definition make_chan_cap {A : Type} (tag : GoTypeTag A) (cap : option nat) : IO (GoChan A) :=
  fun w => let l := w_next w in
           ORet (MkChan l)
                (mkWorld (w_refs w)
                         (fun k => if Nat.eqb k l
                                   then Some (existT _ A (tag, (nil, (false, cap))))
                                   else w_chans w k)
                         (w_maps w) (S l) (w_output w)).
Definition make_chan {A : Type} (tag : GoTypeTag A) : IO (GoChan A) :=
  make_chan_cap tag (Some 0%nat).
(** [make(chan T, n)]: a NEGATIVE runtime size PANICS in Go ([rt_makechan_size]) — [make_chan_buf] FAILS
    LOUD rather than silently repairing it to 0 through [Z.to_nat].  On a non-negative [n] the stored
    capacity is EXACTLY [Z.to_nat (intraw n)] (no clamping happens — [Z.to_nat] is faithful for [n >= 0]). *)
Definition make_chan_buf {A : Type} (tag : GoTypeTag A) (n : GoInt) : IO (GoChan A) :=
  fun w => if (intraw n <? 0)%Z then OPanic rt_makechan_size w
           else make_chan_cap tag (Some (Z.to_nat (intraw n))) w.
(** The channel OPERATIONS ([send]/[recv]/[close_chan]/[recv_ok]/[select_*]/
    [go_spawn]) are DEFINITIONS over the concrete channel STATE below (declared
    after it, so they can reference it); their [run_*] laws and the channel laws
    are THEOREMS — the whole typed-heap channel layer is axiom-free. *)

(** ---- Channels via state in the world (the concurrent denotational model) ----

    Channel semantics rest on STATE, not on bind-sequencing intuition.  Each
    channel has, in the world, a FIFO [chan_buf] (values sent but not yet
    received; head = next to receive) and a [chan_closed] flag.  Sends/receives/
    closes are world-updates ([chan_send_upd] enqueues, [chan_recv_upd] dequeues
    the head, [chan_close_upd] marks closed).  This MIRRORS the map heap model:
    the interface characterises a standard FIFO + flag, hence is satisfiable
    (consistent, non-degenerate), and the channel LAWS below are THEOREMS
    derived from it — not free-standing axioms asserted on intuition.

    BLOCKING is idealised away (like divergence / OOM, and matching [run_io]'s
    totality): a [recv] equation is given only when the buffer is non-empty (or
    the channel is closed); a [recv] on a permanently-empty open channel blocks
    forever, which has no denotation here — a deadlock, out of scope.  This is the
    SEQUENTIAL (single-goroutine, or correctly-synchronised) slice; the
    cross-goroutine HAPPENS-BEFORE partial order is the next layer. *)
(** The channel STATE accessors/updates are DEFINITIONS over [w_chans].
    Because [GoChan A] carries no [GoTypeTag] (that would make
    [GoTypeTag] universe-inconsistent), the typed accessors take the element [tag]
    explicitly; it coerces the cell's stored buffer ([list E]) to the accessor's
    view ([list A]) — they are equal by construction, [tag_eq] recovers the proof.
    [chan_closed] needs no tag (it reads the bool directly). *)
(** The channel STATE accessors treat the NIL sentinel ([ch_loc = 0]) as having NO cell: a nil channel
    reads as canonically EMPTY / OPEN / no-capacity, and NEVER trusts whatever [w_chans 0] happens to hold.
    [ValidWorld] reserves location 0, but the public [mkWorld]/[MkChan] constructors could FORGE a cell
    there; the guard makes a forged loc-0 cell UNOBSERVABLE.  So a nil channel is canonically NEVER-READY
    (empty + open): [recv]/[send] FAIL LOUD (Go blocks forever), and a [select] case on a nil channel NEVER
    FIRES — the other cases or a [default] run instead, and a select blocks (fails loud) only when EVERY case
    is blocked.  No operation ever acts on fabricated loc-0 data. *)
Definition chan_buf {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : list A :=
  if Nat.eqb (ch_loc ch) 0 then nil
  else match w_chans w (ch_loc ch) with
  | Some (existT _ E (etag, (buf, _))) =>
      match tag_eq tag etag with
      | Some p => eq_rect E (fun X : Type => list X) buf A (eq_sym p)
      | None   => nil
      end
  | None => nil
  end.
Definition chan_closed {A : Type} (ch : GoChan A) (w : World) : bool :=
  if Nat.eqb (ch_loc ch) 0 then false
  else match w_chans w (ch_loc ch) with
  | Some (existT _ _ (_, (_, (cl, _)))) => cl
  | None => false
  end.
(** [chan_cap ch w] — the channel's capacity ([None] = unbounded; an absent OR nil cell reads [None]). *)
Definition chan_cap {A : Type} (ch : GoChan A) (w : World) : option nat :=
  if Nat.eqb (ch_loc ch) 0 then None
  else match w_chans w (ch_loc ch) with
  | Some (existT _ _ (_, (_, (_, cap)))) => cap
  | None => None
  end.
(** [chan_present ch w] — is [ch]'s cell ALLOCATED?  FALSE for the nil sentinel ([ch_loc = 0], whose cell is
    unobservable) AND for a nonzero ABSENT location (a forged / dangling handle whose [w_chans] cell is [None]).
    An operation that would CREATE channel state ([send]/[close]) fails loud when this is false, so an
    unallocated handle never fabricates a cell — the general fix for nonzero-absent forgery, beyond loc-0.
    (Tag-AGNOSTIC: cell EXISTENCE is what [chan_room]/[close] need; typed reads still go through [chan_buf].) *)
Definition chan_present {A : Type} (ch : GoChan A) (w : World) : bool :=
  if Nat.eqb (ch_loc ch) 0 then false
  else match w_chans w (ch_loc ch) with Some _ => true | None => false end.
Lemma chan_present_nonnil : forall {A} (ch : GoChan A) w,
  chan_present ch w = true -> Nat.eqb (ch_loc ch) 0 = false.
Proof. intros A ch w H. unfold chan_present in H. destruct (Nat.eqb (ch_loc ch) 0); [ discriminate H | reflexivity ]. Qed.
Lemma chan_closed_true_present : forall {A} (ch : GoChan A) w,
  chan_closed ch w = true -> chan_present ch w = true.
Proof.
  intros A ch w H. unfold chan_closed in H. unfold chan_present.
  destruct (Nat.eqb (ch_loc ch) 0); [ discriminate H | ].
  destruct (w_chans w (ch_loc ch)) as [c|]; [ reflexivity | discriminate H ].
Qed.
(** [chan_room tag ch w] — is there room for one more send?  An UNALLOCATED handle (nil [ch_loc = 0] OR a
    nonzero ABSENT cell) has NO room ([chan_present] false) — Go BLOCKS forever on a nil send and a forged
    handle must not fabricate — so [send] FAILS LOUD ([OPanic rt_chan_send_block]) and never enqueues.
    Otherwise: [None]-capacity (unbounded, the concurrency bridge's ALLOCATED abstract channels) always has
    room; [Some n] iff the FIFO is shorter than [n]. *)
Definition chan_room {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : bool :=
  if chan_present ch w then
    match chan_cap ch w with
    | None   => true
    | Some n => Nat.ltb (List.length (chan_buf tag ch w)) n
    end
  else false.   (* an UNALLOCATED handle (nil OR nonzero-absent) has NO room: [send] fails loud, never fabricates a cell *)
(** CANONICAL NIL STATE: a nil channel ([MkChan 0]) reads as empty / open / no-capacity in ANY world [w],
    including a FORGED one carrying a cell at location 0 — the accessor guards make [w_chans 0] unobservable.
    These are the witnesses that nil-channel reads cannot be tricked by a fabricated loc-0 heap cell. *)
Lemma chan_buf_nil : forall {A} (tag : GoTypeTag A) (w : World), chan_buf tag (MkChan 0) w = nil.
Proof. reflexivity. Qed.
Lemma chan_closed_nil : forall {A} (w : World), chan_closed (@MkChan A 0) w = false.
Proof. reflexivity. Qed.
Lemma chan_cap_nil : forall {A} (w : World), chan_cap (@MkChan A 0) w = None.
Proof. reflexivity. Qed.
(** Write a channel cell at [ch]'s location, tagged with [tag], preserving its capacity [cap].
    ROOT NIL GUARD: location 0 is the reserved nil sentinel (never allocated).  A write there would
    FORGE channel state at an unallocated handle, so it is a NO-OP — the single choke point that makes
    the raw [chan_send_upd]/[chan_recv_upd]/[chan_close_upd] unable to fabricate a loc-0 cell, exactly as
    [map_write] guards the nil map.  (Public [send]/[recv]/[close_chan] already fail loud on nil; this
    seals the raw update primitives too.) *)
Definition chan_write {A : Type} (tag : GoTypeTag A) (ch : GoChan A)
                      (buf : list A) (cl : bool) (cap : option nat) (w : World) : World :=
  if Nat.eqb (ch_loc ch) 0 then w
  else mkWorld (w_refs w)
          (fun k => if Nat.eqb k (ch_loc ch)
                    then Some (existT _ A (tag, (buf, (cl, cap))))
                    else w_chans w k)
          (w_maps w) (w_next w) (w_output w).
Definition chan_send_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World) : World :=
  chan_write tag ch (chan_buf tag ch w ++ (v :: nil)) (chan_closed ch w) (chan_cap ch w) w.
Definition chan_recv_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : World :=
  chan_write tag ch (tl (chan_buf tag ch w)) (chan_closed ch w) (chan_cap ch w) w.
Definition chan_close_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : World :=
  chan_write tag ch (chan_buf tag ch w) true (chan_cap ch w) w.

(** Reading back what [chan_write] wrote (with the SAME tag) — the heap-cell
    round-trip, via [eqb_refl] (location hit) + [tag_eq_refl] (coercion identity).
    The non-nil side condition ([ch_loc <> 0]) is what the ROOT guard demands: a nil write is a
    no-op, so the round-trip holds only for an ALLOCATED handle. *)
Lemma chan_buf_write_same : forall {A} (tag : GoTypeTag A) ch buf cl cap w,
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_buf tag ch (chan_write tag ch buf cl cap w) = buf.
Proof.
  intros A tag ch buf cl cap w Hnn. unfold chan_buf, chan_write. rewrite Hnn. cbn.
  rewrite (Nat.eqb_refl (ch_loc ch)), tag_eq_refl. reflexivity.
Qed.
Lemma chan_closed_write_same : forall {A} (tag : GoTypeTag A) ch buf cl cap w,
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_closed ch (chan_write tag ch buf cl cap w) = cl.
Proof.
  intros A tag ch buf cl cap w Hnn. unfold chan_closed, chan_write. rewrite Hnn. cbn.
  rewrite (Nat.eqb_refl (ch_loc ch)). reflexivity.
Qed.
Lemma chan_cap_write_same : forall {A} (tag : GoTypeTag A) ch buf cl cap w,
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_cap ch (chan_write tag ch buf cl cap w) = cap.
Proof.
  intros A tag ch buf cl cap w Hnn. unfold chan_cap, chan_write. rewrite Hnn. cbn.
  rewrite (Nat.eqb_refl (ch_loc ch)). reflexivity.
Qed.
(** A write to [ch] leaves a DIFFERENT channel's cell ([ch']) untouched — record
    injectivity ([ch <> ch' => ch_loc ch <> ch_loc ch']) + [eqb_false_complete]. *)
Lemma chan_loc_neq : forall {A} (ch ch' : GoChan A), ch <> ch' -> ch_loc ch <> ch_loc ch'.
Proof.
  intros A ch ch' Hne Hloc. apply Hne.
  destruct ch as [l]; destruct ch' as [l']; cbn in Hloc; subst; reflexivity.
Qed.
Lemma chan_read_write_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) buf cl cap w,
  ch <> ch' -> w_chans (chan_write tag ch buf cl cap w) (ch_loc ch') = w_chans w (ch_loc ch').
Proof.
  intros A tag ch ch' buf cl cap w Hne. unfold chan_write.
  destruct (Nat.eqb (ch_loc ch) 0).           (* nil write is a no-op ⇒ frame is trivial *)
  { reflexivity. }
  cbn.
  rewrite (proj2 (Nat.eqb_neq (ch_loc ch') (ch_loc ch))).
  - reflexivity.
  - intro H. apply (chan_loc_neq ch ch' Hne). symmetry; exact H.
Qed.

(** [chan_present] ALGEBRA for the concurrency bridge: a write to a non-nil handle leaves it PRESENT (it
    installs a [Some] cell), and it leaves a DIFFERENT channel's presence unchanged (frame).  So the bridge's
    cell-existence invariant is PRESERVED across [chan_send_upd]/[chan_recv_upd] — the bridge channels stay
    ALLOCATED, never decaying into the absent state that [chan_room]/[send] now reject. *)
Lemma chan_present_write_same : forall {A} (tag : GoTypeTag A) ch buf cl cap w,
  Nat.eqb (ch_loc ch) 0 = false -> chan_present ch (chan_write tag ch buf cl cap w) = true.
Proof.
  intros A tag ch buf cl cap w Hnn. unfold chan_present, chan_write. rewrite Hnn. cbn.
  rewrite Nat.eqb_refl. reflexivity.
Qed.
Lemma chan_present_write_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) buf cl cap w,
  ch <> ch' -> chan_present ch' (chan_write tag ch buf cl cap w) = chan_present ch' w.
Proof.
  intros A tag ch ch' buf cl cap w Hne. unfold chan_present.
  destruct (Nat.eqb (ch_loc ch') 0); [ reflexivity | ].
  rewrite (chan_read_write_frame tag ch ch' buf cl cap w Hne). reflexivity.
Qed.
Lemma chan_present_send : forall {A} (tag : GoTypeTag A) ch v w,
  Nat.eqb (ch_loc ch) 0 = false -> chan_present ch (chan_send_upd tag ch v w) = true.
Proof. intros A tag ch v w Hnn. unfold chan_send_upd. apply chan_present_write_same; exact Hnn. Qed.
Lemma chan_present_recv : forall {A} (tag : GoTypeTag A) ch w,
  Nat.eqb (ch_loc ch) 0 = false -> chan_present ch (chan_recv_upd tag ch w) = true.
Proof. intros A tag ch w Hnn. unfold chan_recv_upd. apply chan_present_write_same; exact Hnn. Qed.
Lemma chan_present_send_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) v w,
  ch <> ch' -> chan_present ch' (chan_send_upd tag ch v w) = chan_present ch' w.
Proof. intros A tag ch ch' v w Hne. unfold chan_send_upd. apply chan_present_write_frame; exact Hne. Qed.
Lemma chan_present_recv_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) w,
  ch <> ch' -> chan_present ch' (chan_recv_upd tag ch w) = chan_present ch' w.
Proof. intros A tag ch ch' w Hne. unfold chan_recv_upd. apply chan_present_write_frame; exact Hne. Qed.

(** Heap-interface laws: how [chan_buf]/[chan_closed] read after each update.  Each carries the
    ROOT-guard side condition [ch_loc <> 0] — on the reserved nil handle the update is a no-op, so the
    read-back holds only for an ALLOCATED channel (the bridge supplies this via [chenv_live]). *)
Theorem chan_buf_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_buf tag ch (chan_send_upd tag ch v w) = chan_buf tag ch w ++ (v :: nil).
Proof. intros A tag ch v w Hnn. unfold chan_send_upd. rewrite chan_buf_write_same by exact Hnn. reflexivity. Qed.
Theorem chan_buf_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (rest : list A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_buf tag ch w = v :: rest -> chan_buf tag ch (chan_recv_upd tag ch w) = rest.
Proof. intros A tag ch v rest w Hnn H. unfold chan_recv_upd. rewrite chan_buf_write_same by exact Hnn. rewrite H. reflexivity. Qed.
Theorem chan_closed_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_closed ch (chan_send_upd tag ch v w) = chan_closed ch w.
Proof. intros A tag ch v w Hnn. unfold chan_send_upd. rewrite chan_closed_write_same by exact Hnn. reflexivity. Qed.
Theorem chan_closed_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_closed ch (chan_recv_upd tag ch w) = chan_closed ch w.
Proof. intros A tag ch w Hnn. unfold chan_recv_upd. rewrite chan_closed_write_same by exact Hnn. reflexivity. Qed.
Theorem chan_closed_close : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_closed ch (chan_close_upd tag ch w) = true.
Proof. intros A tag ch w Hnn. unfold chan_close_upd. rewrite chan_closed_write_same by exact Hnn. reflexivity. Qed.
(** Capacity is INVARIANT under send/recv/close (the cell's [cap] is re-written unchanged) — needed so a
    capacity-aware [send] can reason across updates, and so the [WMatch1] bridge keeps its [None] channels. *)
Theorem chan_cap_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_cap ch (chan_send_upd tag ch v w) = chan_cap ch w.
Proof. intros A tag ch v w Hnn. unfold chan_send_upd. rewrite chan_cap_write_same by exact Hnn. reflexivity. Qed.
Theorem chan_cap_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_cap ch (chan_recv_upd tag ch w) = chan_cap ch w.
Proof. intros A tag ch w Hnn. unfold chan_recv_upd. rewrite chan_cap_write_same by exact Hnn. reflexivity. Qed.
Theorem chan_cap_close : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  Nat.eqb (ch_loc ch) 0 = false ->
  chan_cap ch (chan_close_upd tag ch w) = chan_cap ch w.
Proof. intros A tag ch w Hnn. unfold chan_close_upd. rewrite chan_cap_write_same by exact Hnn. reflexivity. Qed.
(** [chan_room = true] WITNESSES allocation: [chan_room] is false on ANY unallocated handle (nil OR
    nonzero-absent, via [chan_present]), so a channel with room has a PRESENT cell (hence is non-nil).  Lets a
    caller that already has [chan_room = true] discharge the read-back / cell-existence side conditions above. *)
Lemma chan_room_present : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_room tag ch w = true -> chan_present ch w = true.
Proof.
  intros A tag ch w H. unfold chan_room in H.
  destruct (chan_present ch w) eqn:E; [ reflexivity | discriminate H ].
Qed.
Lemma chan_room_nonnil : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_room tag ch w = true -> Nat.eqb (ch_loc ch) 0 = false.
Proof. intros A tag ch w H. exact (chan_present_nonnil ch w (chan_room_present tag ch w H)). Qed.

(** Channel SEPARATION (frame): a send/receive on one channel leaves
    every OTHER channel's buffer untouched (distinct cells are independent). *)
Theorem chan_buf_send_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (v : A) (w : World),
  ch <> ch' -> chan_buf tag ch' (chan_send_upd tag ch v w) = chan_buf tag ch' w.
Proof.
  intros A tag ch ch' v w Hne. unfold chan_send_upd, chan_buf.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.
Theorem chan_buf_recv_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_buf tag ch' (chan_recv_upd tag ch w) = chan_buf tag ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_recv_upd, chan_buf.
  rewrite (chan_read_write_frame tag ch ch' _ _ _ w Hne). reflexivity.
Qed.


(** The channel OPERATIONS, DEFINED over the state above.  Extraction lowers each by
    NAME to Go (the bodies — which mention the proof-only state — are suppressed).
    FAITHFULNESS: [recv] on an open EMPTY channel is a LOUD panic — Go BLOCKS there
    (a deadlock in a single-goroutine [run_io]), which has no synchronous value.
    A CLOSED, drained channel correctly yields the zero value (Go's "receive from a
    closed channel").  ([select] with a [default] is NON-blocking by DESIGN — firing
    [default] on an open-empty channel is FAITHFUL Go; [recv_ok] gets the same
    blocking-panic split below.) *)
(** [send] is CAPACITY-AWARE: a send onto a CLOSED channel panics (Go's "send on closed
    channel"); a send with NO ROOM ([chan_room] false — a full [Some n] buffer, or an UNBUFFERED [Some 0]
    channel with no waiting receiver) FAILS LOUD (Go BLOCKS; the sequential IO model has no rendezvous), it
    does NOT silently over-append; otherwise it enqueues.  [None]-capacity (unbounded) channels always have
    room — used by the concurrency bridge's abstract channels. *)
Definition send {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) : IO unit :=
  fun w => if chan_closed ch w then OPanic rt_send_closed w
           else if chan_room tag ch w then ORet tt (chan_send_upd tag ch v w)
                else OPanic rt_chan_send_block w.
Definition recv {A} (tag : GoTypeTag A) (ch : GoChan A) : IO A :=
  fun w => match chan_buf tag ch w with
           | v :: _ => ORet v (chan_recv_upd tag ch w)
           | nil    => if chan_closed ch w
                       then ORet (zero_val tag) w   (* closed + drained: Go yields the zero value immediately *)
                       else OPanic (anyt TString
                         "fido: recv on an open EMPTY channel blocks — a deadlock in a sequential run_io, with no synchronous value"%string) w
           end.
(** [close] on a NIL channel ([MkChan 0]) PANICS — Go's "close of nil channel" — instead of fabricating a
    close at the reserved location 0.  (Go also panics on a double-close, the [chan_closed] guard below.)
    [send]/[recv] on a nil channel BLOCK FOREVER in Go; the sequential [run_io] has no stuck/divergence
    outcome, so both FAIL LOUD rather than fabricate state: a nil channel has NO room ([chan_room] is false
    for [ch_loc = 0]), so [send] takes its block branch ([OPanic rt_chan_send_block] — it never enqueues /
    writes location 0), and [recv] on a nil (hence empty, open) channel already hits its empty-channel block
    panic.  This is NOT excused as "unreachable": [MkChan 0] is a PUBLIC handle, so nil ops are made fail-loud,
    not assumed away.  Lowered by name ([close(ch)]), golden-stable. *)
(** [close] fails loud on ANY unallocated handle — nil ([ch_loc = 0]) OR nonzero ABSENT (forged/dangling) —
    via [chan_present], so it can never FABRICATE a closed cell at an unallocated location (Go's [close(nil)]
    panic, generalised to the whole no-cell class).  Only an allocated cell reaches the closed-flag check. *)
Definition close_chan {A} (tag : GoTypeTag A) (ch : GoChan A) : IO unit :=
  fun w => if chan_present ch w
           then (if chan_closed ch w then OPanic rt_close_closed w else ORet tt (chan_close_upd tag ch w))
           else OPanic rt_close_nil w.
Definition recv_ok {A B} (tag : GoTypeTag A) (ch : GoChan A) (f : A -> bool -> IO B) : IO B :=
  fun w => match chan_buf tag ch w with
           | v :: _ => f v true (chan_recv_upd tag ch w)
           | nil    => if chan_closed ch w
                       then f (zero_val tag) false w   (* closed + drained: (zero, ok=false) — Go's comma-ok on a closed channel *)
                       else OPanic (anyt TString
                         "fido: recv_ok on an open EMPTY channel blocks — a deadlock in a sequential run_io, with no synchronous value"%string) w
           end.
(** ANTI-FORGERY WITNESSES: on a nil channel ([MkChan 0]) — in ANY world [w], even one forging a cell at
    location 0 — [send] and [recv] FAIL LOUD and never move a value.  Because the accessors read a nil
    handle canonically (empty/open, [chan_*_nil]), these hold by computation, independent of [w_chans 0]. *)
Lemma send_nil : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  run_io (send tag (MkChan 0) v) w = OPanic rt_chan_send_block w.
Proof. reflexivity. Qed.
Lemma recv_nil_no_value : forall {A} (tag : GoTypeTag A) (w : World) (a : A) (w' : World),
  run_io (recv tag (MkChan 0)) w <> ORet a w'.
Proof. intros A tag w a w' H. unfold recv, run_io in H. discriminate H. Qed.
(** An ABSENT cell ([chan_present = false] — nil OR a forged/dangling nonzero location) reads canonically
    empty / open, so [send]/[recv]/[close] on it never move a value or fabricate state.  These GENERALISE the
    [*_nil] witnesses from the loc-0 sentinel to the WHOLE unallocated class (the checkpoint-57 nonzero-absent
    case).  [chan_buf]/[chan_closed] read [nil]/[false] on any absent cell (the [Some] case is [chan_present]). *)
Lemma chan_buf_absent : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_present ch w = false -> chan_buf tag ch w = nil.
Proof.
  intros A tag ch w H. unfold chan_present in H. unfold chan_buf.
  destruct (Nat.eqb (ch_loc ch) 0); [ reflexivity | ].
  destruct (w_chans w (ch_loc ch)) as [c|]; [ discriminate H | reflexivity ].
Qed.
Lemma chan_closed_absent : forall {A} (ch : GoChan A) (w : World),
  chan_present ch w = false -> chan_closed ch w = false.
Proof.
  intros A ch w H. unfold chan_present in H. unfold chan_closed.
  destruct (Nat.eqb (ch_loc ch) 0); [ reflexivity | ].
  destruct (w_chans w (ch_loc ch)) as [c|]; [ discriminate H | reflexivity ].
Qed.
Lemma send_absent : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_present ch w = false -> run_io (send tag ch v) w = OPanic rt_chan_send_block w.
Proof.
  intros A tag ch v w H. unfold send, run_io.
  rewrite (chan_closed_absent ch w H). unfold chan_room. rewrite H. reflexivity.
Qed.
Lemma recv_absent_no_value : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World) (a : A) (w' : World),
  chan_present ch w = false -> run_io (recv tag ch) w <> ORet a w'.
Proof.
  intros A tag ch w a w' H Hr. unfold recv, run_io in Hr.
  rewrite (chan_buf_absent tag ch w H), (chan_closed_absent ch w H) in Hr. discriminate Hr.
Qed.
Definition select_recv2 {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then k1 (zero_val ta) w   (* ch1 CLOSED+drained: recv READY, yields zero (Go) *)
                       else match chan_buf tb ch2 w with
                            | v :: _ => k2 v (chan_recv_upd tb ch2 w)
                            | nil    => if chan_closed ch2 w then k2 (zero_val tb) w  (* ch2 closed+drained: zero *)
                                        else OPanic rt_select_block w  (* both empty+OPEN: FAIL-LOUD (Go blocks; the IO model has no Blocked outcome) — NEVER a fabricated value *)
                            end
           end.
(** [select_recv_default] — recv case + [default].  A CLOSED, DRAINED channel's recv is READY in
    Go (yields the zero value immediately), so [default] is taken ONLY when the channel is empty
    AND OPEN. *)
Definition select_recv_default {A C} (ta : GoTypeTag A) (ch1 : GoChan A)
                                      (k1 : A -> IO C) (d : IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then k1 (zero_val ta) w   (* closed+drained: recv READY, zero *)
                       else d w                                        (* open+empty: default *)
           end.
(** CORRECTNESS — closed-channel readiness (example): on a CLOSED, DRAINED channel the
    recv case fires with the zero value (NOT [default]); on an OPEN, empty channel [default] fires. *)
Lemma select_default_closed :
  forall {A C} (ta : GoTypeTag A) (ch : GoChan A) (k1 : A -> IO C) (d : IO C) (w : World),
    chan_buf ta ch w = nil -> chan_closed ch w = true ->
    select_recv_default ta ch k1 d w = k1 (zero_val ta) w.
Proof. intros A C ta ch k1 d w He Hc. unfold select_recv_default. rewrite He, Hc. reflexivity. Qed.
Lemma select_default_open_empty :
  forall {A C} (ta : GoTypeTag A) (ch : GoChan A) (k1 : A -> IO C) (d : IO C) (w : World),
    chan_buf ta ch w = nil -> chan_closed ch w = false ->
    select_recv_default ta ch k1 d w = d w.
Proof. intros A C ta ch k1 d w He Hc. unfold select_recv_default. rewrite He, Hc. reflexivity. Qed.
(** NIL-CHANNEL SELECT (witnesses, hold in ANY world incl. a forged one): a [select] case on a nil channel
    is NEVER READY, so it never fires from fabricated loc-0 data.  With a [default] the default runs; with no
    default and every case nil, the select fails loud (blocks).  (A nil case is skipped, NOT a loud failure
    in itself — only an all-blocked select fails loud.) *)
Lemma select_default_nil :
  forall {A C} (ta : GoTypeTag A) (k1 : A -> IO C) (d : IO C) (w : World),
    select_recv_default ta (MkChan 0) k1 d w = d w.
Proof. reflexivity. Qed.
Lemma select_recv2_nil_blocks :
  forall {A B C} (ta : GoTypeTag A) (k1 : A -> IO C) (tb : GoTypeTag B) (k2 : B -> IO C) (w : World),
    select_recv2 ta (MkChan 0) k1 tb (MkChan 0) k2 w = OPanic rt_select_block w.
Proof. reflexivity. Qed.

(** ── Select as SENTINEL + goto ──
    [select] factors into a runtime WAIT that returns WHICH case fired plus a pure CFG DISPATCH
    (goto) on that index — no bespoke select control-flow node in the substrate.  [select_wait2]
    is the SENTINEL; [select2] is the canonical DESUGAR ([bind select_wait2] then a [match] on
    the index).  [select2] is the only producer of the sentinel, so a lifted shape is a valid
    select by construction.

    ⚠ SCOPE OF THE THEOREM.  [select_wait2] inherits the [select_recv2] model's behaviour, a
    DETERMINISTIC UNDER-APPROXIMATION of Go's select, so [select2_eq_recv2] proves the desugar
    equals that *idealised model*, NOT equivalence to Go.  Two deviations:
      (1) CHOICE: both channels ready ⇒ it deterministically takes ch1; Go picks pseudo-randomly,
          so native Go does NOT *refine* this function — it is one example scheduler,
          NON-AUTHORITATIVE as a spec.  The authoritative spec is relational/nondeterministic
          ([rstep]); a safety property must hold for EVERY permitted choice.
      (2) BLOCKING: none ready and no default ⇒ Go BLOCKS, which the sequential [IO] model cannot
          represent — so it FAIL-LOUDS ([OPanic rt_select_block], witnessed by
          [select_recv2_both_empty_open_panics] / [select_wait2_both_empty_open_panics]).
          Blocking is NOT divergence: it is a LOCAL non-step ([concurrency.v] models it —
          [Stuck := ~ can_step /\ ~ done] is the GLOBAL deadlock property); in [IO], fail-loud is
          the SOUND stand-in — a proof cannot derive a false result through a blocked select.
    The EXTRACTION is faithful (native Go [select{}]).  A nondeterministic [select_wait] belongs
    in the [rstep] calculus; a unique-ready determinisation is sound only under an
    interference-freedom discipline keeping readiness stable (else a TOCTOU gap).  Tracked in
    SPEC_CONFORMANCE.

    CLOSED-CHANNEL READINESS: a CLOSED, DRAINED channel's recv is READY in Go (yields zero
    immediately).  [select_recv_default]/[select_recv2]/[select_wait2] check [chan_closed]:
    empty+closed ⇒ that recv case fires with the zero value; [default] only on empty+OPEN
    ([select_default_closed] / [select_default_open_empty]).  The relational select reads
    closedness off the TRACE ([closedb]); [rstep_recv_closed]/[rstep_select_closed] step a
    closed-drained recv/select to zero.  The typed↔relational bridge: [det_select_sound],
    [det_select_incomplete], [det_select_complete_unique]/[det_select_exact_unique],
    [select_fire_is_recv_fire] — the deterministic model is fully faithful precisely in the
    unique-ready regime.
    Remainder: ONE composed theorem carrying a [select_recv2] World execution to a permitted
    [rstep_select]; and [rstep] CLOSED-regime determinism needs close-position uniqueness (at
    most one [KClose] per channel).  Until those, the typed [select] is SOUND, with completeness
    pinned to the unique-ready regime. *)
Definition select_wait2 {A} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) : IO (nat * A) :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => ORet (0, v) (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then ORet (0, zero_val ta) w   (* ch1 closed+drained: case 0 fires, zero *)
                       else match chan_buf ta ch2 w with
                            | v :: _ => ORet (1, v) (chan_recv_upd ta ch2 w)
                            | nil    => if chan_closed ch2 w then ORet (1, zero_val ta) w  (* ch2 closed+drained: case 1, zero *)
                                        else OPanic rt_select_block w  (* both empty+OPEN: FAIL-LOUD — Go blocks; never a fabricated case index/value *)
                            end
           end.
Definition select2 {A C} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) (k1 k2 : A -> IO C) : IO C :=
  bind (select_wait2 ta ch1 ch2)
       (fun iv => match fst iv with O => k1 (snd iv) | _ => k2 (snd iv) end).

(** The desugar is faithful TO THE IDEALISED MODEL: select-via-(wait + index-goto) IS
    [select_recv2].  (NOT equivalence to Go — see the ⚠ scope note above.) *)
Theorem select2_eq_recv2 :
  forall {A C} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) (k1 k2 : A -> IO C),
    select2 ta ch1 ch2 k1 k2 =io= select_recv2 ta ch1 k1 ta ch2 k2.
Proof.
  intros A C ta ch1 ch2 k1 k2. intro w.
  unfold select2, select_recv2, select_wait2, bind, run_io.
  destruct (chan_buf ta ch1 w) as [|v1 r1].
  - destruct (chan_closed ch1 w).
    + reflexivity.                                    (* ch1 closed+drained: both → k1 zero *)
    + destruct (chan_buf ta ch2 w) as [|v2 r2].
      * destruct (chan_closed ch2 w); reflexivity.    (* ch2 closed → k2 zero; else both OPanic rt_select_block *)
      * reflexivity.                                  (* ch2 ready *)
  - reflexivity.                                      (* ch1 ready *)
Qed.

(** ── WORLD-level select↔recv bridge.  Go: "if one or more of the communications can proceed, a
    single one ... is chosen."  When the ch1-priority [select_recv2]'s FIRST channel is READY
    (buffered, or closed-and-drained), it behaves EXACTLY like a plain [recv] on that channel —
    [run_io]-equal to [bind (recv ta ch1) k1].  So a ready case makes select reduce to a recv on the
    chosen channel, and select INHERITS [recv]'s [run_io] laws and operational refinement
    ([denote_sim_recv] / [rstep_recv]).  Faithful for the cases that CAN proceed (Go's
    "communication can proceed"); the both-empty-open fall-through FAIL-LOUDS
    ([OPanic rt_select_block]), never fabricates. *)

(* ch1 BUFFERED ⇒ select dequeues ch1's head = recv ch1 >>= k1. *)
Theorem select_recv2_ch1_buffered :
  forall {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) (v : A) (rest : list A) (w : World),
  chan_buf ta ch1 w = v :: rest ->
  run_io (select_recv2 ta ch1 k1 tb ch2 k2) w = run_io (bind (recv ta ch1) k1) w.
Proof. intros A B C ta ch1 k1 tb ch2 k2 v rest w H. unfold select_recv2, recv, bind, run_io. rewrite H. reflexivity. Qed.

(* ch1 CLOSED + drained ⇒ select yields ch1's zero value = recv ch1 >>= k1 (recv returns zero on the
   drained channel — Go's "receive from a closed channel proceeds immediately"). *)
Theorem select_recv2_ch1_closed :
  forall {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) (w : World),
  chan_buf ta ch1 w = nil -> chan_closed ch1 w = true ->
  run_io (select_recv2 ta ch1 k1 tb ch2 k2) w = run_io (bind (recv ta ch1) k1) w.
Proof. intros A B C ta ch1 k1 tb ch2 k2 w He Hc. unfold select_recv2, recv, bind, run_io. rewrite He, Hc. reflexivity. Qed.

(* ch1 EMPTY + OPEN, ch2 BUFFERED ⇒ select falls through to ch2 = recv ch2 >>= k2. *)
Theorem select_recv2_ch2_buffered :
  forall {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) (v : B) (rest : list B) (w : World),
  chan_buf ta ch1 w = nil -> chan_closed ch1 w = false -> chan_buf tb ch2 w = v :: rest ->
  run_io (select_recv2 ta ch1 k1 tb ch2 k2) w = run_io (bind (recv tb ch2) k2) w.
Proof. intros A B C ta ch1 k1 tb ch2 k2 v rest w He1 Hc1 He2. unfold select_recv2, recv, bind, run_io. rewrite He1, Hc1, He2. reflexivity. Qed.

(* ch1 EMPTY + OPEN, ch2 CLOSED + drained ⇒ select yields ch2's zero = recv ch2 >>= k2. *)
Theorem select_recv2_ch2_closed :
  forall {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) (w : World),
  chan_buf ta ch1 w = nil -> chan_closed ch1 w = false ->
  chan_buf tb ch2 w = nil -> chan_closed ch2 w = true ->
  run_io (select_recv2 ta ch1 k1 tb ch2 k2) w = run_io (bind (recv tb ch2) k2) w.
Proof. intros A B C ta ch1 k1 tb ch2 k2 w He1 Hc1 He2 Hc2. unfold select_recv2, recv, bind, run_io. rewrite He1, Hc1, He2, Hc2. reflexivity. Qed.

(** Both channels EMPTY and OPEN (no case can proceed, no default): [select_recv2] /
    [select_wait2] FAIL LOUD ([OPanic rt_select_block]) — a proof that reaches this state hits an
    [OPanic] it must discharge, never a forged value.  Unreachable in the demos ([select_demo]'s
    ch1 is buffered ⇒ [select_recv2_ch1_buffered] fires). *)
Lemma select_recv2_both_empty_open_panics :
  forall {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) (w : World),
  chan_buf ta ch1 w = nil -> chan_closed ch1 w = false ->
  chan_buf tb ch2 w = nil -> chan_closed ch2 w = false ->
  select_recv2 ta ch1 k1 tb ch2 k2 w = OPanic rt_select_block w.
Proof. intros A B C ta ch1 k1 tb ch2 k2 w He1 Hc1 He2 Hc2. unfold select_recv2. rewrite He1, Hc1, He2, Hc2. reflexivity. Qed.
Lemma select_wait2_both_empty_open_panics :
  forall {A} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) (w : World),
  chan_buf ta ch1 w = nil -> chan_closed ch1 w = false ->
  chan_buf ta ch2 w = nil -> chan_closed ch2 w = false ->
  select_wait2 ta ch1 ch2 w = OPanic rt_select_block w.
Proof. intros A ta ch1 ch2 w He1 Hc1 He2 Hc2. unfold select_wait2. rewrite He1, Hc1, He2, Hc2. reflexivity. Qed.

(** [go_spawn m] (Go spec "Go statements") — FAILS LOUD in the sequential [run_io] semantics.
    A goroutine is CONCURRENT, not a synchronous call: sequentialising the child, importing its
    effects unsynchronised, or erasing a child panic would each make [run_io] theorems false of Go.
    There is no [run_io]<->calculus bridge for spawn (it deliberately has NO [run_io] law — see
    concurrency.v), so the sequential meaning is a LOUD panic: a source-level proof that tries to
    compute a spawn program's [run_io] result hits this wall.  The FAITHFUL spawn lives in the
    concurrent transition system — [rstep_spawn] (concurrency.v).  Extraction is unaffected: the
    plugin lowers [go_spawn] BY NAME to a real [go func(){…}()] statement (body suppressed), so
    the emitted Go is genuinely concurrent. *)
Definition go_spawn (m : IO unit) : IO unit :=
  fun w => OPanic (anyt TString "fido: go_spawn has no sequential run_io meaning — a goroutine is concurrent, not a synchronous call; the faithful semantics is rstep_spawn in concurrency.v"%string) w.

(** The [run_*] laws are THEOREMS, conditioned on channel state.  [send]/
    [recv]/[close_chan] carry the element [tag] (the typed-heap accessors need it
    since [GoChan] is tag-free). *)
Lemma run_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false -> chan_room tag ch w = true ->
  run_io (send tag ch v) w = ORet tt (chan_send_upd tag ch v w).
Proof. intros A tag ch v w H Hr. unfold send, run_io. rewrite H, Hr. reflexivity. Qed.
(** A send with NO room FAILS LOUD (the model has no Blocked outcome). *)
Lemma run_send_blocked : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false -> chan_room tag ch w = false ->
  run_io (send tag ch v) w = OPanic rt_chan_send_block w.
Proof. intros A tag ch v w H Hr. unfold send, run_io. rewrite H, Hr. reflexivity. Qed.
Lemma run_send_closed : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = true ->
  run_io (send tag ch v) w = OPanic rt_send_closed w.
Proof. intros A tag ch v w H. unfold send, run_io. rewrite H. reflexivity. Qed.
Lemma run_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (rest : list A) (w : World),
  chan_buf tag ch w = v :: rest ->
  run_io (recv tag ch) w = ORet v (chan_recv_upd tag ch w).
Proof. intros A tag ch v rest w H. unfold recv, run_io. rewrite H. reflexivity. Qed.
Lemma run_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (v : A) (rest : list A) (w : World),
  chan_buf tag ch w = v :: rest ->
  run_io (recv_ok tag ch f) w = run_io (f v true) (chan_recv_upd tag ch w).
Proof. intros A B tag ch f v rest w H. unfold recv_ok, run_io. rewrite H. reflexivity. Qed.
Lemma run_recv_ok_closed_empty : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (w : World),
  chan_buf tag ch w = nil -> chan_closed ch w = true ->
  run_io (recv_ok tag ch f) w = run_io (f (zero_val tag) false) w.
Proof. intros A B tag ch f w H Hc. unfold recv_ok, run_io. rewrite H, Hc. reflexivity. Qed.
Lemma run_close : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_present ch w = true ->
  chan_closed ch w = false ->
  run_io (close_chan tag ch) w = ORet tt (chan_close_upd tag ch w).
Proof. intros A tag ch w Hp H. unfold close_chan, run_io. rewrite Hp, H. reflexivity. Qed.
(** Closing a non-nil CLOSED channel panics with "close of closed channel" (the CAUSE distinguishes this from "close of nil channel" — an unallocated handle hits the [chan_present] guard).  [chan_closed = true]
    already implies the cell is present ([chan_closed_true_present]); [close_chan_nil] / [close_absent] cover the no-cell ones. *)
Lemma run_close_closed : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch w = true ->
  run_io (close_chan tag ch) w = OPanic rt_close_closed w.
Proof. intros A tag ch w H. unfold close_chan, run_io. rewrite (chan_closed_true_present ch w H), H. reflexivity. Qed.
(** Faithfulness: [close] on a nil channel PANICS with "close of nil channel", exactly Go's [close(nil)]. *)
Lemma close_chan_nil : forall {A} (tag : GoTypeTag A) (w : World),
  run_io (close_chan tag (@MkChan A 0)) w = OPanic rt_close_nil w.
Proof. reflexivity. Qed.
(** ANTI-FORGERY (nonzero-absent generalisation of [close_chan_nil]): [close] on ANY unallocated handle
    ([chan_present = false] — nil OR a forged/dangling nonzero location) FAILS LOUD with NO mutation (the world
    is returned unchanged in the [OPanic]) — it never fabricates a closed cell at an absent location. *)
Lemma close_absent : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_present ch w = false ->
  run_io (close_chan tag ch) w = OPanic rt_close_nil w.
Proof. intros A tag ch w H. unfold close_chan, run_io. rewrite H. reflexivity. Qed.

(** ---- The channel laws, DERIVED as theorems ---- *)

(** After [send ch v] into an OPEN, EMPTY channel, the next [recv] returns [v].
    (Conditions: send must not panic on a closed channel, and FIFO means [recv]
    returns [v] only when [v] is at the head — i.e. the buffer was empty before
    the send.) *)
Theorem send_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false -> chan_buf tag ch w = nil -> chan_room tag ch w = true ->
  run_io (bind (send tag ch v) (fun _ => recv tag ch)) w
  = ORet v (chan_recv_upd tag ch (chan_send_upd tag ch v w)).
Proof.
  intros A tag ch v w Hclosed Hempty Hroom.
  rewrite run_bind, (run_send tag ch v w Hclosed Hroom). cbn.
  apply (run_recv tag ch v nil).
  rewrite (chan_buf_send tag ch v w (chan_room_nonnil tag ch w Hroom)), Hempty. reflexivity.
Qed.

(** [recv_ok] variant: after [send ch v] into an open, empty channel, [recv_ok]
    delivers [(v, true)] and runs the continuation in the dequeued world. *)
Theorem send_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A)
    (f : A -> bool -> IO B) (w : World),
  chan_closed ch w = false -> chan_buf tag ch w = nil -> chan_room tag ch w = true ->
  run_io (bind (send tag ch v) (fun _ => recv_ok tag ch f)) w
  = run_io (f v true) (chan_recv_upd tag ch (chan_send_upd tag ch v w)).
Proof.
  intros A B tag ch v f w Hclosed Hempty Hroom.
  rewrite run_bind, (run_send tag ch v w Hclosed Hroom). cbn.
  apply (run_recv_ok tag ch f v nil).
  rewrite (chan_buf_send tag ch v w (chan_room_nonnil tag ch w Hroom)), Hempty. reflexivity.
Qed.

(** [make_chan] is UNBUFFERED ([Some 0]), so an IO send to a freshly-made unbuffered channel FAILS LOUD
    ([rt_chan_send_block]) — Go blocks pending a receiver — rather than silently over-appending.
    (The capacity-faithfulness witness [make_chan_buf_caps], and the fresh-handle-is-non-nil witness
    [make_chan_nonzero], live in [GoHeap.v] where [ValidWorld] FORCES the allocator's [w_next <> 0]
    — the honest home for allocation reasoning, alongside [ptr_new_nonzero]/[map_make_typed_nonzero].) *)
Lemma make_chan_unbuffered_send_blocks : forall {A} (tag : GoTypeTag A) (v : A) (w : World) ch w',
  run_io (make_chan tag) w = ORet ch w' -> run_io (send tag ch v) w' = OPanic rt_chan_send_block w'.
Proof.
  intros A tag v w ch w' H. unfold make_chan, make_chan_cap, run_io in H.
  injection H as Hch Hw. subst ch w'. unfold send, run_io, chan_closed, chan_room, chan_present, chan_cap, chan_buf. cbn.
  (* [chan_room] is false on EITHER arm: an unallocated ([w_next = 0]) handle is [chan_present = false] (no
     room), and a fresh unbuffered ([Some 0]) buffer is full — so send blocks regardless of [w_next]'s value. *)
  destruct (Nat.eqb (w_next w) 0); cbn; rewrite ?Nat.eqb_refl; cbn; reflexivity.
Qed.
(** FAIL-LOUD witness: [make(chan T, n)] with a NEGATIVE runtime size PANICS ([rt_makechan_size]) — the
    model never silently clamps a negative capacity to 0.  (Positive [n]: [make_chan_buf_caps] in [GoHeap.v]
    witnesses the stored capacity is EXACTLY [Z.to_nat (intraw n)], forced by [ValidWorld].) *)
Lemma make_chan_buf_neg_panics : forall {A} (tag : GoTypeTag A) (n : GoInt) (w : World),
  (intraw n < 0)%Z -> run_io (make_chan_buf tag n) w = OPanic rt_makechan_size w.
Proof.
  intros A tag n w Hneg. unfold make_chan_buf, run_io.
  rewrite (proj2 (Z.ltb_lt (intraw n) 0) Hneg). reflexivity.
Qed.

(** Sending on a closed channel panics (Go spec): close then send → panic.  (On a non-nil channel — a
    nil one would panic at the first [close].) *)
Theorem send_closed_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_present ch w = true ->
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => send tag ch v)) w
  = OPanic rt_send_closed (chan_close_upd tag ch w).
Proof.
  intros A tag ch v w Hp Hopen.
  rewrite run_bind, (run_close tag ch w Hp Hopen). cbn.
  exact (run_send_closed tag ch v (chan_close_upd tag ch w)
           (chan_closed_close tag ch w (chan_present_nonnil ch w Hp))).
Qed.

(** Closing an already-closed channel panics (Go spec): close then close → panic.  (On a non-nil
    channel — a nil one would panic at the first [close].) *)
Theorem double_close_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_present ch w = true ->
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => close_chan tag ch)) w
  = OPanic rt_close_closed (chan_close_upd tag ch w).
Proof.
  intros A tag ch w Hp Hopen.
  rewrite run_bind, (run_close tag ch w Hp Hopen). cbn.
  exact (run_close_closed tag ch (chan_close_upd tag ch w)
           (chan_closed_close tag ch w (chan_present_nonnil ch w Hp))).
Qed.

(** [recv_ok] on a closed, EMPTY channel returns [(zero_val tag, false)] — Go's
    "receive from a closed channel" rule.  This could NOT be an unconditional
    axiom (with [send_recv_ok] it forces [v = zero_val tag] for all [v], an
    inconsistency); conditioning on the channel state makes it sound. *)
Theorem recv_ok_closed_empty : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (w : World),
  chan_buf tag ch w = nil -> chan_closed ch w = true ->
  run_io (recv_ok tag ch f) w = run_io (f (zero_val tag) false) w.
Proof. intros. apply run_recv_ok_closed_empty; assumption. Qed.

(** ---- Happens-before: the partial order on channel events (go.dev/ref/mem) ----

    The ORDERING that race/deadlock-freedom rest on.
    An event is the START or COMPLETION of the n-th send / n-th receive on a
    channel of capacity [cap].  [hb cap] is the transitive closure of the
    primitive edges: program order within each endpoint, plus the two go-mem
    channel rules — "a send is synchronised before the corresponding receive
    completes" and "the k-th receive is synchronised before the (k+cap)-th send
    completes" (the unbuffered rendezvous is the [cap = 0] case).  Start vs
    completion events are distinct precisely so the unbuffered case (send⤳recv
    AND recv⤳send) does not cycle.

    CONSISTENCY IS BY CONSTRUCTION — NO new axioms.  A concrete timestamp [ev_ts]
    is a linear extension of every edge, so [hb] strictly increases [ev_ts] and is
    therefore irreflexive (acyclic).  Crucially [hb] is the closure of EXACTLY the
    real edges — not the total timestamp order — so it adds no spurious ordering,
    which is what keeps it sound for race freedom (concurrent events stay
    unordered).  Transitivity is a constructor; the go-mem rules are theorems.

    Scope: this is one channel's event order; the data-race layer ties events to
    heap accesses below. *)
Inductive ChEvent : Type :=
  | SendStart : nat -> ChEvent | SendDone : nat -> ChEvent
  | RecvStart : nat -> ChEvent | RecvDone : nat -> ChEvent.

Inductive hb_edge (cap : nat) : ChEvent -> ChEvent -> Prop :=
  | hbe_send_po   : forall n, hb_edge cap (SendStart n) (SendDone n)         (* a send starts before it completes *)
  | hbe_recv_po   : forall n, hb_edge cap (RecvStart n) (RecvDone n)
  | hbe_send_seq  : forall n, hb_edge cap (SendDone n) (SendStart (S n))     (* sender program order *)
  | hbe_recv_seq  : forall n, hb_edge cap (RecvDone n) (RecvStart (S n))     (* receiver program order *)
  (* go-mem rule: a send is synchronised before the corresponding receive completes *)
  | hbe_send_recv : forall n, hb_edge cap (SendStart n) (RecvDone n)
  (* go-mem rule: the kth receive is synchronised before the (k+cap)th send completes *)
  | hbe_recv_send : forall k, hb_edge cap (RecvStart k) (SendDone (k + cap)).

Inductive hb (cap : nat) : ChEvent -> ChEvent -> Prop :=
  | hb_one   : forall a b, hb_edge cap a b -> hb cap a b
  | hb_seq   : forall a b c, hb cap a b -> hb cap b c -> hb cap a c.

Definition ev_ts (e : ChEvent) : nat :=
  match e with
  | SendStart n => 4 * n     | SendDone n => 4 * n + 2
  | RecvStart n => 4 * n + 1 | RecvDone n => 4 * n + 3
  end.

Lemma hb_edge_ts : forall cap a b, hb_edge cap a b -> ev_ts a < ev_ts b.
Proof. intros cap a b H; destruct H; cbn; lia. Qed.

(** Every happens-before edge strictly increases the timestamp — so [ev_ts] is a
    valid linear extension and [hb] is acyclic. *)
Theorem hb_ts_increasing : forall cap a b, hb cap a b -> ev_ts a < ev_ts b.
Proof.
  intros cap a b H; induction H as [a b Hedge | a b c Hab IHab Hbc IHbc].
  - exact (hb_edge_ts cap a b Hedge).
  - lia.
Qed.

(** Happens-before is a STRICT PARTIAL ORDER: irreflexive (via the linear
    extension) and transitive (a constructor). *)
Theorem hb_irrefl : forall cap e, ~ hb cap e e.
Proof. intros cap e H. apply hb_ts_increasing in H. lia. Qed.
Theorem hb_transitive : forall cap a b c, hb cap a b -> hb cap b c -> hb cap a c.
Proof. intros cap a b c Hab Hbc. eapply hb_seq; eassumption. Qed.

(** The go-mem channel ordering rules, as theorems. *)
Theorem hb_send_before_recv : forall cap n, hb cap (SendStart n) (RecvDone n).
Proof. intros cap n. apply hb_one. apply hbe_send_recv. Qed.
Theorem hb_recv_before_send : forall cap k, hb cap (RecvStart k) (SendDone (k + cap)).
Proof. intros cap k. apply hb_one. apply hbe_recv_send. Qed.

(** UNBUFFERED rendezvous ([cap = 0]): send and receive are mutually ordered
    across start/completion (the handoff), with NO cycle since [hb] is
    irreflexive.  This is exactly the pair of edges that would be inconsistent if
    start and completion were the same event. *)
Example unbuffered_rendezvous :
  hb 0 (SendStart 0) (RecvDone 0) /\ hb 0 (RecvStart 0) (SendDone 0).
Proof.
  split.
  - apply hb_send_before_recv.
  - exact (hb_recv_before_send 0 0).
Qed.

(** A second invariant captures the CAPACITY relationship: a receive at index [k]
    authorises sends only up to index [k + cap].  [ev_credit] is WEAKLY increasing
    along every edge (it is exactly conserved by the capacity edge), so
    [hb cap a b -> ev_credit a <= ev_credit b].  Unlike [ev_ts] (a linear
    extension, too coarse to witness NON-order), [ev_credit] separates concurrent
    events — which is what proves the model does not over-order. *)
Definition ev_credit (cap : nat) (e : ChEvent) : nat :=
  match e with
  | SendStart n => n     | SendDone n => n
  | RecvStart k => k + cap | RecvDone k => k + cap
  end.

Lemma hb_credit_mono : forall cap a b, hb cap a b -> ev_credit cap a <= ev_credit cap b.
Proof.
  intros cap a b H; induction H as [a b Hedge | a b c Hab IHab Hbc IHbc].
  - destruct Hedge; cbn; lia.
  - lia.
Qed.

(** BUFFERED ([cap = 2]): the sender may complete its 2nd send before the 1st
    receive — so [RecvStart 0] and [SendDone 1] are CONCURRENT (neither
    happens-before the other).  The model does NOT over-order them, which is
    exactly what makes a race-freedom statement on the unsynchronised fragment
    meaningful. *)
Example buffered_sender_runs_ahead :
  ~ hb 2 (RecvStart 0) (SendDone 1).
Proof.
  intro H. apply (hb_credit_mono 2) in H. cbn in H. lia.
Qed.

(** ---- Data races, and channel synchronisation that prevents them ----

    A DATA RACE (go.dev/ref/mem) is two accesses to the SAME memory location, at
    least one a WRITE, UNORDERED by happens-before.  The generic guarantee is that happens-before
    ordering IS the whole defence ([hb_ordered_no_race]); the concrete result is
    that the channel-handoff pattern orders a conflicting write/read pair through
    the [send ⤳ recv] rule, so it does not race — channel synchronisation = race
    freedom.  (This is the canonical message-passing case; whole-PROGRAM race
    freedom additionally needs that every shared access is so ordered — a
    program-level obligation, the next layer.) *)
Inductive Access := AWrite (loc : nat) | ARead (loc : nat).
Definition acc_loc (a : Access) : nat := match a with AWrite l => l | ARead l => l end.
Definition is_write (a : Access) : bool := match a with AWrite _ => true | ARead _ => false end.

(** Two accesses CONFLICT: same location, at least one a write. *)
Definition conflict (a b : Access) : Prop :=
  acc_loc a = acc_loc b /\ (is_write a = true \/ is_write b = true).

(** A DATA RACE: conflicting accesses UNORDERED by happens-before.  Generic over
    the [hb] relation and the per-event access labelling. *)
Definition data_race {E} (hb : E -> E -> Prop) (acc : E -> Access) (e1 e2 : E) : Prop :=
  conflict (acc e1) (acc e2) /\ ~ hb e1 e2 /\ ~ hb e2 e1.

(** Happens-before ordering IS the defence: ordered events never race. *)
Theorem hb_ordered_no_race {E} (hb : E -> E -> Prop) (acc : E -> Access) (e1 e2 : E) :
  hb e1 e2 -> ~ data_race hb acc e1 e2.
Proof. intros Hhb [_ [Hno _]]. exact (Hno Hhb). Qed.

(** The canonical message-passing pattern: goroutine A writes location [x] then
    sends on a channel; goroutine B receives then reads [x].  Edges: program order
    in each goroutine, plus the channel rule [mp_sync] (send synchronised
    before the corresponding receive completes — the [hbe_send_recv] instance). *)
Inductive MPEvent := WriteA | SendA | RecvB | ReadB.
Inductive mp_hb : MPEvent -> MPEvent -> Prop :=
  | mp_po_A  : mp_hb WriteA SendA                         (* A: write x, then send *)
  | mp_sync  : mp_hb SendA RecvB                          (* channel: send ⤳ recv completes *)
  | mp_po_B  : mp_hb RecvB ReadB                          (* B: recv, then read x *)
  | mp_trans : forall a b c, mp_hb a b -> mp_hb b c -> mp_hb a c.
Definition mp_acc (e : MPEvent) : Access :=
  match e with WriteA => AWrite 0 | ReadB => ARead 0 | _ => ARead 1 end.  (* x = location 0 *)

(** The write and the read DO conflict (same location, one is a write)... *)
Example mp_conflict : conflict (mp_acc WriteA) (mp_acc ReadB).
Proof. cbn. split; [reflexivity | left; reflexivity]. Qed.
(** ...yet they are happens-before ordered through the channel handoff... *)
Theorem mp_write_before_read : mp_hb WriteA ReadB.
Proof.
  eapply mp_trans; [apply mp_po_A | eapply mp_trans; [apply mp_sync | apply mp_po_B]].
Qed.
(** ...so the conflicting pair does NOT form a data race.  The channel
    send/receive established happens-before, which is exactly race freedom. *)
Theorem mp_no_race : ~ data_race mp_hb mp_acc WriteA ReadB.
Proof. apply hb_ordered_no_race. exact mp_write_before_read. Qed.

(** ---- Program-level race freedom (the whole-program guarantee) ----

    Lifting the single-pair result to a whole program.  A program is its events,
    each carrying an access [acc], a goroutine id [gid], and the happens-before
    order [hb].  A RACE is two events in DIFFERENT goroutines whose accesses
    conflict and are unordered by [hb] (the [gid e1 <> gid e2] clause also makes
    an event never race itself, and same-goroutine accesses — program-ordered —
    never race).  [RaceFree] is the absence of any race.

    [racefree_of_ordered] is the foundational proof rule (axiom-free): to show a
    whole program race-free, show EVERY cross-goroutine conflicting pair is
    happens-before ordered.  The message-passing program is the first instance:
    whole-program race-free. *)
Definition Race {E} (hb : E -> E -> Prop) (acc : E -> Access) (gid : E -> nat)
                (e1 e2 : E) : Prop :=
  gid e1 <> gid e2 /\ conflict (acc e1) (acc e2) /\ ~ hb e1 e2 /\ ~ hb e2 e1.

Definition RaceFree {E} (hb : E -> E -> Prop) (acc : E -> Access) (gid : E -> nat) : Prop :=
  forall e1 e2, ~ Race hb acc gid e1 e2.

(** Foundational rule: all cross-goroutine conflicts ordered ⇒ race-free.
    (The converse holds classically; this constructive direction is the one a
    verification discharges, so it stays axiom-free.) *)
Theorem racefree_of_ordered {E} (hb : E -> E -> Prop) (acc : E -> Access) (gid : E -> nat) :
  (forall e1 e2, gid e1 <> gid e2 -> conflict (acc e1) (acc e2) -> hb e1 e2 \/ hb e2 e1) ->
  RaceFree hb acc gid.
Proof.
  intros H e1 e2 [Hg [Hc [H12 H21]]].
  destruct (H e1 e2 Hg Hc) as [Hhb | Hhb]; [exact (H12 Hhb) | exact (H21 Hhb)].
Qed.

(** The message-passing PROGRAM (goroutine 0 = {write, send}, goroutine 1 =
    {recv, read}) is whole-program race-free: its only cross-goroutine conflict
    (the write/read of [x]) is ordered by the channel handoff. *)
Definition mp_gid (e : MPEvent) : nat :=
  match e with WriteA => 0 | SendA => 0 | RecvB => 1 | ReadB => 1 end.

Theorem mp_program_race_free : RaceFree mp_hb mp_acc mp_gid.
Proof.
  apply racefree_of_ordered. intros e1 e2 Hg Hc.
  destruct e1, e2; cbn in *;
    try (exfalso; apply Hg; reflexivity);
    try (exfalso; destruct Hc as [Hl _]; discriminate Hl);
    try (exfalso; destruct Hc as [_ [Hw|Hw]]; discriminate Hw).
  - left.  exact mp_write_before_read.
  - right. exact mp_write_before_read.
Qed.

(** ---- The 4th go-mem channel rule — close ⤳ a receive returning zero ----

    The open model ([hb cap]) covers rules 1/3/4 for unbounded communication.  The
    remaining rule — "the closing of a channel is synchronized before a receive that
    returns a zero value because the channel is closed" — needs a FINITE scenario:
    the sender sends [nsent] values then CLOSES; the receiver receives unboundedly.
    Receive [n < nsent] gets the nth value (rule 1); receive [n >= nsent] returns
    ZERO (closed + drained) and is synchronised AFTER the close (rule 2).  Its own
    event type keeps the open model untouched; same axiom-free technique — a
    timestamp [ev_ts_c] (linear extension ⇒ irreflexive) and a CONSERVED credit
    [ev_credit_c] (⇒ no over-ordering).  Crucially the close is ordered before the
    ZERO-returning receives ONLY, never the value-receives, so it adds no spurious
    order.  Send/recv/recv-send edges carry [< nsent] guards (they exist only for the
    sends that actually happen). *)
Inductive ChEvC : Type :=
  | CSendStart : nat -> ChEvC | CSendDone : nat -> ChEvC
  | CRecvStart : nat -> ChEvC | CRecvDone : nat -> ChEvC
  | CClose : ChEvC.

Inductive hbc_edge (cap nsent : nat) : ChEvC -> ChEvC -> Prop :=
  | hbce_send_po    : forall n, n < nsent     -> hbc_edge cap nsent (CSendStart n) (CSendDone n)
  | hbce_recv_po    : forall n,                  hbc_edge cap nsent (CRecvStart n) (CRecvDone n)
  | hbce_send_seq   : forall n, S n < nsent   -> hbc_edge cap nsent (CSendDone n) (CSendStart (S n))
  | hbce_recv_seq   : forall n,                  hbc_edge cap nsent (CRecvDone n) (CRecvStart (S n))
  | hbce_send_recv  : forall n, n < nsent     -> hbc_edge cap nsent (CSendStart n) (CRecvDone n)
  | hbce_recv_send  : forall k, k + cap < nsent -> hbc_edge cap nsent (CRecvStart k) (CSendDone (k + cap))
  (* sender program order: the close comes after the last send *)
  | hbce_send_close : forall n, S n = nsent   -> hbc_edge cap nsent (CSendDone n) CClose
  (* rule 2: close ⤳ every receive that returns zero (index >= nsent) *)
  | hbce_close_recv : forall n, nsent <= n    -> hbc_edge cap nsent CClose (CRecvDone n).

Inductive hbc (cap nsent : nat) : ChEvC -> ChEvC -> Prop :=
  | hbc_one : forall a b, hbc_edge cap nsent a b -> hbc cap nsent a b
  | hbc_seq : forall a b c, hbc cap nsent a b -> hbc cap nsent b c -> hbc cap nsent a c.

Definition ev_ts_c (nsent : nat) (e : ChEvC) : nat :=
  match e with
  | CSendStart n => 4 * n     | CSendDone n => 4 * n + 2
  | CRecvStart n => 4 * n + 1 | CRecvDone n => 4 * n + 3
  | CClose       => 4 * nsent
  end.

Lemma hbc_edge_ts : forall cap nsent a b,
  hbc_edge cap nsent a b -> ev_ts_c nsent a < ev_ts_c nsent b.
Proof. intros cap nsent a b H; destruct H; cbn; lia. Qed.

Theorem hbc_ts_increasing : forall cap nsent a b,
  hbc cap nsent a b -> ev_ts_c nsent a < ev_ts_c nsent b.
Proof.
  intros cap nsent a b H; induction H as [a b Hedge | a b c Hab IHab Hbc IHbc].
  - exact (hbc_edge_ts cap nsent a b Hedge).
  - lia.
Qed.

Theorem hbc_irrefl : forall cap nsent e, ~ hbc cap nsent e e.
Proof. intros cap nsent e H. apply hbc_ts_increasing in H. lia. Qed.

(** Rule 2 as a THEOREM: close is synchronised before every zero-returning receive. *)
Theorem hbc_close_before_zero_recv :
  forall cap nsent n, nsent <= n -> hbc cap nsent CClose (CRecvDone n).
Proof. intros cap nsent n H. apply hbc_one. apply hbce_close_recv. exact H. Qed.

(** ...and the close follows the last send (sender program order). *)
Theorem hbc_send_before_close :
  forall cap nsent n, S n = nsent -> hbc cap nsent (CSendDone n) CClose.
Proof. intros cap nsent n H. apply hbc_one. apply hbce_send_close. exact H. Qed.

Definition ev_credit_c (cap nsent : nat) (e : ChEvC) : nat :=
  match e with
  | CSendStart n => n       | CSendDone n => n
  | CRecvStart k => k + cap  | CRecvDone k => k + cap
  | CClose       => nsent
  end.

Lemma hbc_credit_mono : forall cap nsent a b,
  hbc cap nsent a b -> ev_credit_c cap nsent a <= ev_credit_c cap nsent b.
Proof.
  intros cap nsent a b H; induction H as [a b Hedge | a b c Hab IHab Hbc IHbc].
  - destruct Hedge; cbn; lia.
  - lia.
Qed.

(** NO OVER-ORDERING: the close is NOT synchronised before a receive that returns a
    VALUE (index < nsent).  With [nsent = 5], close does not happen-before the 0th
    receive (which gets a real value) — they are concurrent, exactly as in Go (the
    receiver may take value 0 before the sender closes). *)
Example close_not_before_value_recv : ~ hbc 0 5 CClose (CRecvDone 0).
Proof. intro H. apply (hbc_credit_mono 0 5) in H. cbn in H. lia. Qed.

(** ---- The goroutine FORK edge ----

    go-mem: "the go statement that starts a new goroutine is synchronized before the
    start of the goroutine's execution."  So a value the parent writes BEFORE the
    [go] is visible to the child with NO channel — the fork alone orders it.  The
    canonical case (parent writes [x] then spawns a child that reads [x]) is
    whole-program race-free purely by the fork edge.  (Reuses the generic
    [Race]/[RaceFree]/[racefree_of_ordered] — axiom-free.) *)
Inductive ForkEvent := FkWrite | FkGo | FkStart | FkRead.
Inductive fork_hb : ForkEvent -> ForkEvent -> Prop :=
  | fk_po_parent : fork_hb FkWrite FkGo        (* parent: write x, then go *)
  | fk_fork      : fork_hb FkGo FkStart        (* go ⤳ child's start *)
  | fk_po_child  : fork_hb FkStart FkRead       (* child: start, then read x *)
  | fk_trans : forall a b c, fork_hb a b -> fork_hb b c -> fork_hb a c.
Definition fork_acc (e : ForkEvent) : Access :=
  match e with FkWrite => AWrite 0 | FkRead => ARead 0 | _ => ARead 1 end.  (* x = location 0 *)
Definition fork_gid (e : ForkEvent) : nat :=
  match e with FkWrite => 0 | FkGo => 0 | FkStart => 1 | FkRead => 1 end.
Theorem fork_write_before_read : fork_hb FkWrite FkRead.
Proof.
  eapply fk_trans; [apply fk_po_parent | eapply fk_trans; [apply fk_fork | apply fk_po_child]].
Qed.
Theorem fork_program_race_free : RaceFree fork_hb fork_acc fork_gid.
Proof.
  apply racefree_of_ordered. intros e1 e2 Hg Hc.
  destruct e1, e2; cbn in *;
    try (exfalso; apply Hg; reflexivity);
    try (exfalso; destruct Hc as [Hl _]; discriminate Hl);
    try (exfalso; destruct Hc as [_ [Hw|Hw]]; discriminate Hw).
  - left.  exact fork_write_before_read.
  - right. exact fork_write_before_read.
Qed.

(** ---- STRUCT CHANNELS (a 2-field [int64 x int64] struct over a channel) ----

    A struct channel is a [GoChan (GoI64 * GoI64)]: the CELL stores the field TUPLE, tagged by the
    DECIDABLE [TProd TI64 TI64] (a product is canonical, so [tag_eq] recovers it — a nominal
    [GoTypeTag] for a NAMED struct is impossible, [tag_eq] cannot decide it).  The value sent IS the
    tuple, so the channel marshals it by the IDENTITY.

    COHERENCE — there is NO [StructRep] to choose, so a send and a receive CANNOT disagree on
    field order: marshalling by the identity makes a swapped-rep corruption UNREPRESENTABLE
    (the non-overridable behaviour of a Go [chan (int64,int64)]).  A named 2-field struct over
    a channel would need a nominal struct tag (unavailable) — out of scope, not approximated.

    *(Extraction of the idiomatic native [chan R] / [ch <- p] / [<-ch] is a separate slice: Coq's
    [prod] is the multi-return tuple, so emitting it as a Go struct needs dedicated plugin work;
    this lands the MODEL + the correctness theorem.)* *)
Definition struct_make2 (n : GoInt) : IO (GoChan (GoI64 * GoI64)) :=
  bind (make_chan_buf (TProd TI64 TI64) n) (fun ch => ret (MkChan (ch_loc ch))).
Definition struct_send2 (ch : GoChan (GoI64 * GoI64)) (v : GoI64 * GoI64) : IO unit :=
  send (TProd TI64 TI64) (MkChan (ch_loc ch)) v.
Definition struct_recv2 (ch : GoChan (GoI64 * GoI64)) : IO (GoI64 * GoI64) :=
  recv (TProd TI64 TI64) (MkChan (ch_loc ch)).

(** CORRECTNESS — round-trip faithfulness.  On an OPEN, EMPTY channel, [struct_send2] then
    [struct_recv2] recovers the struct EXACTLY: the field-tuple marshalling is lossless, by
    [sr2_eta] of the channel's CANONICAL rep (send and recv share it — no rep to mismatch).  This
    is the acceptance test at the model level (a struct survives a channel round-trip intact). *)
Theorem struct_chan_roundtrip2 :
  forall (ch : GoChan (GoI64 * GoI64)) (v : GoI64 * GoI64) (w : World),
    @chan_closed (GoI64 * GoI64)%type (MkChan (ch_loc ch)) w = false ->
    chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch)) w = nil ->
    chan_room (TProd TI64 TI64) (MkChan (ch_loc ch)) w = true ->
    exists w', run_io (bind (struct_send2 ch v)
                            (fun _ => struct_recv2 ch)) w = ORet v w'.
Proof.
  intros ch v w Hopen Hempty Hroom.
  unfold struct_send2, struct_recv2.
  rewrite run_bind.
  rewrite (run_send (TProd TI64 TI64) (MkChan (ch_loc ch)) v w Hopen Hroom).
  assert (Hbuf1 : chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch))
            (chan_send_upd (TProd TI64 TI64) (MkChan (ch_loc ch)) v w) = v :: nil)
    by (rewrite (chan_buf_send (TProd TI64 TI64) (MkChan (ch_loc ch)) v w
                   (chan_room_nonnil (TProd TI64 TI64) (MkChan (ch_loc ch)) w Hroom)), Hempty; reflexivity).
  rewrite (run_recv (TProd TI64 TI64) (MkChan (ch_loc ch)) v nil _ Hbuf1).
  eexists; reflexivity.
Qed.
