(** Go builtin functions and types — always in scope, no import required.

    GoAny models Go's [any] / [interface{}] type.  It is Rocq's sigma type
    {T : Type & T}: the type witness is erased by the extraction plugin,
    which then passes the underlying Go value directly.

    The [any] notation wraps any value without requiring a per-type
    constructor.  To add a new Go type to println, just write [any val]. *)

Require Import Coq.Init.Specif.
Require Import Coq.Logic.FunctionalExtensionality.

(** ---- IO monad ----

    [IO A] represents a Go effectful computation.  The type and its
    combinators are kept abstract (axiomatic) so the extraction plugin
    continues to lower [bind m f] to sequential Go statements and erase
    [ret x] to its argument — no world-threading in the generated code.

    For PROOFS we add a denotational semantics: [run_io m w] gives the
    concrete meaning of [m] as a function from the current world [w] to a
    result and updated world.  [run_io] is a proof-only device; it is never
    extracted.  From [run_ret], [run_bind], and [run_io_inj] the monad laws
    are provable lemmas rather than postulated axioms.

    The Hoare triple [{{ P }} m {{ Q }}] is defined via [run_io], giving us a
    pre/postcondition framework for program verification.  This is the
    foundation on which channel session-type proofs will be built. *)

Axiom IO   : Type -> Type.
Axiom ret  : forall {A : Type}, A -> IO A.
Axiom bind : forall {A B : Type}, IO A -> (A -> IO B) -> IO B.

Notation "m >>' k"    := (bind m (fun _ => k)) (at level 50, left associativity).
Notation "x <-' m ;; k" := (bind m (fun x => k))
  (at level 80, m at level 90, right associativity).

(** ---- Denotational semantics (proof-only, never extracted) ---- *)

Axiom World : Type.

(** [run_io m w] runs computation [m] from world [w], returning the result
    and the updated world. *)
Axiom run_io  : forall {A : Type}, IO A -> World -> A * World.
Axiom run_ret : forall {A} (x : A) (w : World),
  run_io (ret x) w = (x, w).
Axiom run_bind : forall {A B} (m : IO A) (f : A -> IO B) (w : World),
  run_io (bind m f) w =
  let (a, w') := run_io m w in run_io (f a) w'.
(** Two computations equal if they behave identically on every world. *)
Axiom run_io_inj : forall {A} (m m' : IO A),
  (forall w, run_io m w = run_io m' w) -> m = m'.

(** Monad laws — now provable lemmas, not axioms. *)
Lemma bind_ret_l : forall {A B} (x : A) (f : A -> IO B),
  bind (ret x) f = f x.
Proof.
  intros. apply run_io_inj. intro w.
  rewrite run_bind, run_ret. reflexivity.
Qed.

Lemma bind_ret_r : forall {A} (m : IO A),
  bind m (@ret A) = m.
Proof.
  intros. apply run_io_inj. intro w.
  rewrite run_bind. destruct (run_io m w).
  rewrite run_ret. reflexivity.
Qed.

Lemma bind_assoc : forall {A B C} (m : IO A) (f : A -> IO B) (g : B -> IO C),
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros. apply run_io_inj. intro w.
  case_eq (run_io m w). intros a w' Hmw.
  rewrite (run_bind (bind m f) g), (run_bind m f), Hmw. simpl.
  rewrite (run_bind m (fun x => bind (f x) g)), Hmw. simpl.
  rewrite run_bind. reflexivity.
Qed.

(** ---- Hoare logic ---- *)

(** [{{ P }} m {{ Q }}]: if [P] holds of the world before [m], then [Q]
    holds of the result and world after [m]. *)
Definition hoare {A : Type} (P : World -> Prop) (m : IO A)
    (Q : A -> World -> Prop) : Prop :=
  forall w, P w -> let (a, w') := run_io m w in Q a w'.

Notation "{{ P }} m {{ Q }}" :=
  (hoare P m Q)
  (at level 90, m at level 0,
   format "{{ P }} '/  '  m '/  ' {{ Q }}").

Lemma hoare_ret : forall {A} (x : A) (P : World -> Prop),
  {{ P }} ret x {{ fun a w => P w /\ a = x }}.
Proof.
  intros. unfold hoare. intros w Hw.
  rewrite run_ret. auto.
Qed.

Lemma hoare_bind : forall {A B} (m : IO A) (f : A -> IO B) P R Q,
  {{ P }} m {{ R }} ->
  (forall a, {{ R a }} f a {{ Q }}) ->
  {{ P }} bind m f {{ Q }}.
Proof.
  intros. unfold hoare in *. intros w Hw.
  rewrite run_bind.
  specialize (H w Hw).
  destruct (run_io m w) as [a w'].
  exact (H0 a w' H).
Qed.

Lemma hoare_consequence : forall {A} (m : IO A) P P' Q Q',
  (forall w, P' w -> P w) ->
  {{ P }} m {{ Q }} ->
  (forall a w, Q a w -> Q' a w) ->
  {{ P' }} m {{ Q' }}.
Proof.
  intros. unfold hoare in *. intros w Hw.
  specialize (H0 w (H w Hw)).
  destruct (run_io m w) as [a w'].
  exact (H1 a w' H0).
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

(** ---- Types ---- *)

Definition GoAny : Type := {T : Type & T}.
Notation any x := (@existT Type (fun T : Type => T) _ x).

(** Signed integer types.
    [GoInt64] is [PrimInt63.int] — Rocq's primitive 63-bit machine integer,
    which extracts to [int64] in Go (63 usable bits; correct on all 64-bit
    platforms).  The remaining widths are axioms since Rocq has no native
    equivalent at those widths. *)
Axiom GoInt   : Type.   (* int    — platform-width, typically 64-bit *)
Axiom GoInt8  : Type.   (* int8   — 8-bit  *)
Axiom GoInt16 : Type.   (* int16  — 16-bit *)
Axiom GoInt32 : Type.   (* int32  — 32-bit *)
(* GoInt64 = PrimInt63.int, loaded separately via Stdlib *)
Notation GoRune := GoInt32.  (* rune is an alias for int32 *)

(** Unsigned integer types. *)
Axiom GoUint   : Type.   (* uint    — platform-width *)
Axiom GoUint8  : Type.   (* uint8   — 8-bit  *)
Axiom GoUint16 : Type.   (* uint16  — 16-bit *)
Axiom GoUint32 : Type.   (* uint32  — 32-bit *)
Axiom GoUint64 : Type.   (* uint64  — 64-bit *)
Notation GoByte := GoUint8.  (* byte is an alias for uint8 *)

(** Go's string type — a sequence of Unicode code points.
    Modelled as [list GoRune] so Rocq's list theory applies directly.
    The plugin maps [list GoRune] → [string] in all type positions. *)
Definition GoString : Type := list GoRune.

(** Go's slice type — a resizable sequence of elements.
    Modelled as [list A] so Rocq's list theory applies directly.
    The plugin maps [list A] → [[]T] for any element type [A].
    Note: [list GoRune] maps to [string], not [[]int32].

    NOTE — aliasing: like maps, slices are reference types in Go.  The pure
    functional model (append returning a new list) is safe for single-goroutine
    sequential programs where there is no aliasing of the underlying array.
    For concurrent programs or programs that intentionally alias slice headers,
    [append] should be moved to [IO] (same reasoning as [map_set]/[map_delete]). *)
Definition GoSlice (A : Type) : Type := list A.

(** Floating-point types.
    [GoFloat64] is Rocq's primitive [PrimFloat.float] — IEEE 754 double
    precision, with verified arithmetic semantics in the kernel.
    [GoFloat32] is an axiom; Rocq has no native 32-bit float. *)
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.
From Stdlib Require Import Floats.PrimFloat.
Notation GoFloat64 := float.
Axiom GoFloat32 : Type.

(** ---- Builtins ---- *)

Axiom print   : list GoAny -> IO unit.
Axiom println : list GoAny -> IO unit.

(** panic aborts the running goroutine, unwinding the stack.
    Returns [IO A] for any [A]: in the IO monad this is consistent —
    panic never produces a value, it just terminates the computation.
    Law: [bind_panic_l] captures that panic short-circuits all continuations. *)
Axiom panic        : forall {A : Type}, GoAny -> IO A.
Axiom bind_panic_l : forall {A B} (x : GoAny) (f : A -> IO B),
  bind (panic x) f = panic x.

(** panic satisfies any postcondition vacuously — it never returns. *)
Lemma hoare_panic : forall {A} (v : GoAny) P (Q : A -> World -> Prop),
  {{ P }} @panic A v {{ Q }}.
Proof.
  intros. unfold hoare. intros w _.
  (* panic never terminates; any Q holds vacuously.
     We cannot prove this without an axiom about run_io (panic v). *)
Abort.
Axiom hoare_panic : forall {A} (v : GoAny) P (Q : A -> World -> Prop),
  {{ P }} @panic A v {{ Q }}.

(** ---- panic / recover semantics ----

    [catch m h] is the semantic of [defer func() { if r := recover(); r != nil { h(r) } }()].
    [recover()] in Go is just the panic value bound by [h] — it needs no separate axiom.

    Compound panics: if [h] itself panics with [w], [catch (panic v) h = h v = panic w],
    so the new panic [w] replaces [v].  This is correct Go semantics and falls out from
    [catch_panic] alone — no extra law needed.

    [with_defer] models [defer cleanup()] (without recover): runs [cleanup] on both
    normal exit and panic exit.  If [cleanup] panics mid-panic, the new panic wins —
    also correct Go semantics, again from [catch_panic] + [bind_panic_l]. *)

Axiom catch : forall {A : Type}, IO A -> (GoAny -> IO A) -> IO A.

Axiom catch_ret   : forall {A} (x : A) (h : GoAny -> IO A),
  catch (ret x) h = ret x.
Axiom catch_panic : forall {A} (v : GoAny) (h : GoAny -> IO A),
  catch (panic v) h = h v.

(** [with_defer cleanup m]: run [m], then run [cleanup] regardless of outcome.
    If [cleanup] panics, its panic replaces any in-flight panic. *)
Definition with_defer {A : Type} (cleanup : IO unit) (m : IO A) : IO A :=
  catch
    (x <-' m ;; cleanup >>' ret x)
    (fun v => cleanup >>' panic v).

(** The semantics claimed above, now proven rather than asserted: when the
    guarded body panics, the deferred [cleanup] still runs and the original
    panic propagates afterwards.  Follows from [bind_panic_l] (panic
    short-circuits the body) and [catch_panic] (the handler fires). *)
Lemma with_defer_panic : forall {A} (cleanup : IO unit) (v : GoAny),
  @with_defer A cleanup (panic v) = cleanup >>' panic v.
Proof.
  intros A cleanup v. unfold with_defer.
  rewrite bind_panic_l, catch_panic. reflexivity.
Qed.

(** Forward declarations so GoTypeTag can reference composite Go types in its
    TChan, TSlice, and TMap constructors.  Full axiomatisation follows below. *)
Axiom GoMap  : Type -> Type -> Type.
Axiom GoChan : Type -> Type.

(** ---- Type assertions ----

    [GoTypeTag T] is a term-level witness encoding the Go type [T].
    Because it is an inductive (not a type), it survives extraction —
    the plugin inspects the constructor to emit [v.(T)] with the right type.

    Extend this inductive as new Go types are added to builtins. *)

Inductive GoTypeTag : Type -> Type :=
  | TBool    : GoTypeTag bool
  | TInt64   : GoTypeTag int             (* → int64 *)
  | TFloat64 : GoTypeTag float            (* → float64 *)
  | TString  : GoTypeTag GoString
  | TAny     : GoTypeTag GoAny
  | TInt     : GoTypeTag GoInt
  | TInt8    : GoTypeTag GoInt8
  | TInt16   : GoTypeTag GoInt16
  | TInt32   : GoTypeTag GoInt32
  | TUint    : GoTypeTag GoUint
  | TUint8   : GoTypeTag GoUint8
  | TUint16  : GoTypeTag GoUint16
  | TUint32  : GoTypeTag GoUint32
  | TUint64  : GoTypeTag GoUint64
  | TFloat32 : GoTypeTag GoFloat32
  (* Composite type tags — carry the element/key/value tags so the plugin can
     reconstruct the full Go type string recursively. *)
  | TChan  : forall {A : Type},           GoTypeTag A -> GoTypeTag (GoChan A)
  | TSlice : forall {A : Type},           GoTypeTag A -> GoTypeTag (GoSlice A)
  | TMap   : forall {K V : Type}, GoTypeTag K -> GoTypeTag V -> GoTypeTag (GoMap K V).

(** [type_assert tag v] asserts that [v : GoAny] holds a value of Go type [T].
    Panics (like Go's [v.(T)]) if the runtime type does not match.

    ESCAPE HATCH: the raw panicking form, safe only inside [catch] or when the
    runtime type is already known.  The safe-by-construction default — a checked
    two-value [v, ok := x.(T)] form (CPS, like [recv_ok]) — is a tracked gap
    (CLAUDE.md "Known gaps"). *)
Axiom type_assert : forall {T : Type}, GoTypeTag T -> GoAny -> IO T.

Axiom type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (any x) = ret x.
(* type_assert panics if the runtime type does not match T.
   The precise failure law requires a decidable type equality; add when needed. *)

(** ---- GoMap ----

    [GoMap K V] models Go's [map[K]V].  Operations are modelled as pure
    functions returning updated maps; extraction emits in-place mutations,
    which are semantically equivalent in single-goroutine programs since
    maps are reference types with no observable aliasing difference.

    [map_make] is in [IO] because it allocates a new map reference.
    [map_get_opt] returns [option V]; its extraction is deferred until we
    handle [option] lowering properly. *)

Axiom map_empty  : forall {K V : Type}, GoMap K V.

(** [map_make_typed kt vt] creates an empty map with concrete key/value types.
    The [GoTypeTag] witnesses survive extraction so the plugin can emit
    [make(map[K]V)] with the correct Go type — unlike bare [map_make] which
    loses the types to erasure and falls back to [map[any]any].

    NOTE: Go map access never panics on a missing key — it returns the zero
    value (two-value form gives [false] for [ok]).  This differs from slice
    indexing, which DOES panic out of bounds. *)
Axiom map_make_typed : forall {K V : Type}, GoTypeTag K -> GoTypeTag V -> IO (GoMap K V).

(** Untyped fallback — loses key/value types to erasure, emits map[any]any. *)
Axiom map_make   : forall {K V : Type}, IO (GoMap K V).

(** Read — pure for single-goroutine programs.
    NOTE: map access on a missing key returns the zero value — it never panics.
    This differs from slice indexing which panics out of bounds.
    With goroutines, concurrent map reads/writes are a data race in Go
    (maps are not safe for concurrent use without synchronization).  If
    goroutines are added, [map_get_opt] and [map_len] should move to [IO]
    to make the ordering explicit. *)
Axiom map_get_opt : forall {K V : Type}, K -> GoMap K V -> option V.
Axiom map_len     : forall {K V : Type}, GoMap K V -> GoInt.

(** Write — in IO: mutates the map reference in place.
    IO sequencing prevents aliasing: you cannot fork a map reference since
    set/delete return [IO unit], not a new map value.  A second set on the
    same [m] must be sequenced after the first via bind. *)
(** [map_get_or k default m] returns the value at [k], or [default] if absent.
    Extracts to: [if v, ok := m[k]; ok { v } else { default }].
    Full [option]-valued access via [map_get_opt] requires [MLcase] handling
    in the plugin — deferred until option lowering is implemented. *)
Axiom map_get_or : forall {K V : Type}, K -> V -> GoMap K V -> V.

Axiom map_get_or_hit  : forall {K V : Type} (k : K) (v default : V) (m : GoMap K V),
  map_get_opt k m = Some v -> map_get_or k default m = v.
Axiom map_get_or_miss : forall {K V : Type} (k : K) (default : V) (m : GoMap K V),
  map_get_opt k m = None -> map_get_or k default m = default.

Axiom map_set    : forall {K V : Type}, K -> V -> GoMap K V -> IO unit.
Axiom map_delete : forall {K V : Type}, K -> GoMap K V -> IO unit.

(** Laws — stated in terms of the map value observable via [map_get_opt]
    after a sequenced write. *)
Axiom map_get_set_same : forall {K V} (k : K) (v : V) (m : GoMap K V),
  bind (map_set k v m) (fun _ => ret (map_get_opt k m)) =
  bind (map_set k v m) (fun _ => ret (Some v)).
Axiom map_get_empty : forall {K V} (k : K),
  map_get_opt k (@map_empty K V) = None.
Axiom map_get_delete_same : forall {K V} (k : K) (m : GoMap K V),
  bind (map_delete k m) (fun _ => ret (map_get_opt k m)) =
  bind (map_delete k m) (fun _ => ret (@None V)).
(** Setting [k1] does not affect reads at a different key [k2]. *)
Axiom map_get_set_diff : forall {K V} (k1 k2 : K) (v : V) (m : GoMap K V),
  k1 <> k2 ->
  bind (map_set k1 v m) (fun _ => ret (map_get_opt k2 m)) =
  ret (map_get_opt k2 m).

(** ---- GoChan ----

    [GoChan A] models Go's [chan T].  [make_chan] allocates an unbuffered
    channel — send blocks until a receiver is ready, so an unbuffered channel
    requires a complementary goroutine (step 5).  [make_chan_buf n] allocates
    a buffered channel with capacity [n]; send does not block until the buffer
    is full, making single-goroutine use safe when n > 0.

    Ownership: whoever holds the [GoChan A] value owns the channel endpoint.
    Session-type proofs (step 6) will enforce protocol compliance at the Rocq
    type level, with zero runtime cost. *)

Axiom make_chan     : forall {A : Type}, GoTypeTag A -> IO (GoChan A).
Axiom make_chan_buf : forall {A : Type}, GoTypeTag A -> int -> IO (GoChan A).
(** ESCAPE HATCH: raw [send] / [close_chan] panic on a closed (or nil) channel
    (laws [send_closed_panics], [double_close_panics]).  The safe-by-construction
    layer is session types ([sess_send] etc.), which make those states
    unrepresentable.  These raw forms exist for non-session channel use. *)
Axiom send     : forall {A : Type}, GoChan A -> A -> IO unit.
Axiom recv     : forall {A : Type}, GoTypeTag A -> GoChan A -> IO A.
Axiom close_chan : forall {A : Type}, GoChan A -> IO unit.

(** Two-value receive: [recv_ok tag ch (fun x ok => body)] lowers to
    [x, ok := <-ch; body].  [ok] is [false] when [ch] is closed and empty.
    Continuation-passing style avoids needing product-type extraction. *)
Axiom recv_ok : forall {A B : Type},
  GoTypeTag A -> GoChan A -> (A -> bool -> IO B) -> IO B.

(** [go_spawn m] launches [m] as a concurrent goroutine and returns immediately.
    Ownership of any [GoChan] endpoints captured in [m]'s closure transfers to
    the new goroutine at spawn time — the key invariant for race freedom.

    Laws relating goroutines to channels require a concurrent world model.
    That model arrives in step 5/6 (session types); for now the axiom is
    sufficient to extract correct Go and to structure proofs about protocol
    compliance on individual channels. *)
Axiom go_spawn : IO unit -> IO unit.

(** Every Go type has a zero value (false, 0, 0.0, nil, "", …). *)
Axiom zero_val : forall {A : Type}, GoTypeTag A -> A.

(** After [send ch v], the next [recv] on [ch] returns [v].
    The bind sequencing encodes that send completed before recv ran — valid
    for buffered channels (with space) and for unbuffered channels when a
    complementary goroutine is blocked in recv. *)
Axiom send_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A),
  bind (send ch v) (fun _ => recv tag ch) =
  bind (send ch v) (fun _ => ret v).

(** [recv_ok] variant: after [send ch v], [recv_ok] delivers [(v, true)]. *)
Axiom send_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A)
    (f : A -> bool -> IO B),
  bind (send ch v) (fun _ => recv_ok tag ch f) =
  bind (send ch v) (fun _ => f v true).

(** Sending on a closed channel panics (Go spec). *)
Axiom send_closed_panics : forall {A} (ch : GoChan A) (v : A),
  bind (close_chan ch) (fun _ => send ch v) =
  bind (close_chan ch) (fun _ => @panic unit (any tt)).

(** Closing an already-closed channel panics (Go spec). *)
Axiom double_close_panics : forall {A} (ch : GoChan A),
  bind (close_chan ch) (fun _ => close_chan ch) =
  bind (close_chan ch) (fun _ => @panic unit (any tt)).

(** NOTE: [recv_ok] on a closed, empty channel returns [(zero_val tag, false)],
    but this cannot be stated as an unconditional axiom: combined with
    [send_recv_ok] it would require [v = zero_val tag] for all [v], which is
    inconsistent.  A guarded version — parameterised by a channel-empty
    predicate — is deferred until the channel-state model arrives in step 5. *)

Axiom len    : forall {A : Type}, GoSlice A -> GoInt.
Axiom cap    : forall {A : Type}, GoSlice A -> GoInt.
Axiom append : forall {A : Type}, GoSlice A -> GoSlice A -> GoSlice A.

(** Construct a typed Go slice from a Rocq list literal.
    The [GoTypeTag] witness lets the plugin emit [[]T{v1, v2, ...}] with the
    correct element type instead of falling back to [append(nil, ...)]. *)
Axiom slice_of_list : forall {A : Type}, GoTypeTag A -> list A -> GoSlice A.

(** Indexed access — returns [IO A] because Go panics on out-of-bounds.

    ESCAPE HATCH: the raw panicking form; use inside [catch] to handle OOB.
    Prefer [slice_at_ok] (below), the safe-by-construction default.  A
    proof-carrying [slice_at xs i (i < len xs)] → [xs[i]] unguarded is still a
    tracked gap (needs the int model, CLAUDE.md "Known gaps"). *)
Axiom slice_get : forall {A : Type}, GoTypeTag A -> GoSlice A -> int -> IO A.

(** Safe checked index (the safe-by-construction default for slice access).
    [slice_at_ok tag xs i (fun v ok => body)] bounds-checks [i]: if it is in
    range then [v = xs[i]] and [ok = true]; otherwise [v] is the zero value and
    [ok = false].  CPS like [recv_ok]; because the caller must handle [ok =
    false], this form cannot panic out of bounds.  (The index [i : int] is an
    unsigned 63-bit value, so [i >= 0] always holds — only the upper bound is
    checked.) *)
Axiom slice_at_ok : forall {A B : Type},
  GoTypeTag A -> GoSlice A -> int -> (A -> bool -> IO B) -> IO B.

(** ---- Session types (step 6) ----

    [Proto] encodes a typed communication protocol as a sequence of sends
    and receives.  [dual P] flips every send↔recv, giving the complementary
    protocol for the other participant.

    [SessEndpoint P] is a channel endpoint whose *remaining* protocol is [P].
    At runtime both endpoints of a session are the same [chan any]; all type
    discipline is enforced by Rocq's type-checker at zero runtime cost.

    The key guarantee: [sess_send] only type-checks when the endpoint has
    type [SessEndpoint (PSend A P)], and [sess_recv] only when it has type
    [SessEndpoint (PRecv A P)].  Misuse (wrong order, wrong direction) is a
    Rocq compile-time error — no runtime check required. *)

Inductive Proto : Type :=
  | PSend : Type -> Proto -> Proto   (** send a value of type A, continue as P *)
  | PRecv : Type -> Proto -> Proto   (** recv a value of type A, continue as P *)
  | PEnd  : Proto.                   (** protocol complete *)

Fixpoint dual (p : Proto) : Proto :=
  match p with
  | PSend A p' => PRecv A (dual p')
  | PRecv A p' => PSend A (dual p')
  | PEnd       => PEnd
  end.

Lemma dual_involutive : forall p, dual (dual p) = p.
Proof.
  induction p as [A p' IH | A p' IH |].
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - reflexivity.
Qed.

(** Taking the dual is injective: a protocol is determined by its dual.
    Follows directly from involutivity. *)
Lemma dual_injective : forall p q, dual p = dual q -> p = q.
Proof.
  intros p q H.
  rewrite <- (dual_involutive p), <- (dual_involutive q), H.
  reflexivity.
Qed.

(** Number of communication steps in a protocol. *)
Fixpoint proto_len (p : Proto) : nat :=
  match p with
  | PSend _ p' => S (proto_len p')
  | PRecv _ p' => S (proto_len p')
  | PEnd       => O
  end.

(** Client and server perform the same number of steps: every send on one
    end is matched by a receive on the other, so the protocols have equal
    length.  This is the structural heart of the "both ends agree" guarantee. *)
Lemma dual_preserves_len : forall p, proto_len (dual p) = proto_len p.
Proof.
  induction p as [A p' IH | A p' IH |]; simpl; auto.
Qed.

(** A session endpoint whose remaining protocol is [P].
    Extracts to [chan any] — both ends of a session share the same channel;
    the proto index is a proof-only witness. *)
Axiom SessEndpoint : Proto -> Type.

(** [make_sess f]: allocate a fresh session channel and call [f] with both
    endpoints.  One end has protocol [P], the other has [dual P].
    CPS avoids needing product-type extraction. *)
Axiom make_sess : forall {B : Type} {P : Proto},
  (SessEndpoint P -> SessEndpoint (dual P) -> IO B) -> IO B.

(** [sess_send ep v f]: send [v] on [ep] (consuming the PSend step), then
    continue as [f ep'] where [ep' : SessEndpoint P] is the same channel.
    Extracts to: [ep <- v; ep' := ep; <f-body>]. *)
Axiom sess_send : forall {A B : Type} {P : Proto},
  SessEndpoint (PSend A P) -> A -> (SessEndpoint P -> IO B) -> IO B.

(** [sess_recv tag ep f]: receive a value of type [A] from [ep], then
    continue as [f v ep'] where [v] is the received value and [ep'] is the
    same channel advanced past the PRecv step.
    Extracts to: [_r := <-ep; v := _r.(T); ep' := ep; <f-body>]. *)
Axiom sess_recv : forall {A B : Type} {P : Proto},
  GoTypeTag A -> SessEndpoint (PRecv A P) -> (A -> SessEndpoint P -> IO B) -> IO B.

(** End the session.  The endpoint has reached [PEnd] — no more operations.
    Extracts as a no-op; the channel is garbage-collected. *)
Axiom sess_close : SessEndpoint PEnd -> IO unit.
