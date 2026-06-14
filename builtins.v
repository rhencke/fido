(** Go builtin functions and types — always in scope, no import required.

    GoAny models Go's [any] / [interface{}] type.  It is Rocq's sigma type
    {T : Type & T}: the type witness is erased by the extraction plugin,
    which then passes the underlying Go value directly.

    The [any] notation wraps any value without requiring a per-type
    constructor.  To add a new Go type to println, just write [any val]. *)

Require Import Coq.Init.Specif.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.   (* app / tl for the channel FIFO buffer model *)
From Stdlib Require Import Lia.   (* happens-before timestamp arithmetic *)

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

(** ---- Types: [GoAny] (Go's [any]/[interface{}]) ----
    Hoisted up here because [panic]'s argument and the panic-aware denotational
    semantics below both mention it. *)
Definition GoAny : Type := {T : Type & T}.
Notation any x := (@existT Type (fun T : Type => T) _ x).

(** ---- panic / recover ----
    [panic v] aborts the goroutine with value [v]; it has type [IO A] for any
    [A] because it never returns a value, it short-circuits.  [catch m h] is the
    semantics of [defer func(){ if r := recover(); r != nil { h(r) } }()]: run
    [m]; if it panics with [v], run [h v]; else pass [m]'s result through.
    Declared here (before [run_io]) so the semantics can give panic a proper
    *outcome* rather than conflating it with a returned value. *)
Axiom panic : forall {A : Type}, GoAny -> IO A.
Axiom catch : forall {A : Type}, IO A -> (GoAny -> IO A) -> IO A.

(** ---- Denotational semantics (proof-only, never extracted) ----

    [run_io m w] gives the meaning of [m] from world [w] as an OUTCOME: either
    [ORet a w'] (normal completion, result [a], new world [w']) or [OPanic v w']
    (the goroutine panicked with value [v]).  Modelling panic as an outcome —
    not as a total [A * World] — is essential.  With the old total type, the law
    "[panic] satisfies every postcondition" was satisfiable ONLY by making
    [World] empty (machine-checked: it entailed [World -> False]), which
    collapsed the whole layer — every [IO A] provably equal, every Hoare triple
    vacuous.  As an honest outcome, panic leaves [World] inhabited and the Hoare
    logic meaningful.  DIVERGENCE is idealised away: [run_io] is total, i.e. the
    model assumes every computation terminates (out of scope, like OOM) — the
    claim is "given termination and sufficient resources". *)
Axiom World : Type.

Inductive Outcome (A : Type) : Type :=
  | ORet   : A -> World -> Outcome A
  | OPanic : GoAny -> World -> Outcome A.
Arguments ORet {A} _ _.
Arguments OPanic {A} _ _.

Axiom run_io  : forall {A : Type}, IO A -> World -> Outcome A.
Axiom run_ret : forall {A} (x : A) (w : World),
  run_io (ret x) w = ORet x w.
Axiom run_bind : forall {A B} (m : IO A) (f : A -> IO B) (w : World),
  run_io (bind m f) w =
  match run_io m w with
  | ORet a w'   => run_io (f a) w'
  | OPanic v w' => OPanic v w'        (* panic short-circuits the continuation *)
  end.
Axiom run_panic : forall {A} (v : GoAny) (w : World),
  run_io (@panic A v) w = OPanic v w.
Axiom run_catch : forall {A} (m : IO A) (h : GoAny -> IO A) (w : World),
  run_io (catch m h) w =
  match run_io m w with
  | ORet a w'   => ORet a w'          (* normal: pass through, handler not run *)
  | OPanic v w' => run_io (h v) w'    (* panic: run the handler on the value *)
  end.
(** Two computations are equal if they behave identically on every world. *)
Axiom run_io_inj : forall {A} (m m' : IO A),
  (forall w, run_io m w = run_io m' w) -> m = m'.

(** ---- Monad laws — provable lemmas, not axioms. ---- *)
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
  rewrite run_bind. destruct (run_io m w) as [a w' | v w'].
  - rewrite run_ret. reflexivity.
  - reflexivity.
Qed.

Lemma bind_assoc : forall {A B C} (m : IO A) (f : A -> IO B) (g : B -> IO C),
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite (run_bind (bind m f) g), (run_bind m f),
          (run_bind m (fun x => bind (f x) g)).
  destruct (run_io m w) as [a w' | v w'].
  - rewrite (run_bind (f a) g). reflexivity.
  - reflexivity.
Qed.

(** [panic] short-circuits any continuation — PROVED from [run_panic]
    (was an axiom). *)
Lemma bind_panic_l : forall {A B} (x : GoAny) (f : A -> IO B),
  bind (panic x) f = panic x.
Proof.
  intros. apply run_io_inj. intro w.
  (* the two [panic]s are at different type instances ([IO A] vs [IO B]),
     so [!run_panic] is needed to rewrite both. *)
  rewrite run_bind, !run_panic. reflexivity.
Qed.

(** [catch] laws — PROVED from [run_catch] (were axioms). *)
Lemma catch_ret : forall {A} (x : A) (h : GoAny -> IO A),
  catch (ret x) h = ret x.
Proof.
  intros. apply run_io_inj. intro w.
  rewrite run_catch, !run_ret. reflexivity.
Qed.

Lemma catch_panic : forall {A} (v : GoAny) (h : GoAny -> IO A),
  catch (panic v) h = h v.
Proof.
  intros. apply run_io_inj. intro w.
  rewrite run_catch, run_panic. reflexivity.
Qed.

(** ---- Hoare logic ----
    [{{ P }} m {{ Q }}] is PARTIAL correctness for NORMAL completion: if [P]
    holds before and [m] returns normally ([ORet a w']) then [Q a w'].  A panic
    outcome satisfies the triple trivially ([True]) — honestly, since partial
    correctness asserts nothing about abnormal exit.  This is [True], NOT
    [False]: that is exactly what keeps [hoare_panic] from collapsing [World]. *)
Definition hoare {A : Type} (P : World -> Prop) (m : IO A)
    (Q : A -> World -> Prop) : Prop :=
  forall w, P w -> match run_io m w with
                   | ORet a w'  => Q a w'
                   | OPanic _ _ => True
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
  - exact I.
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
  - exact I.
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

(** panic satisfies any postcondition — PROVED, and WITHOUT collapsing [World]
    (the panic outcome maps to [True], not [False]). *)
Lemma hoare_panic : forall {A} (v : GoAny) P (Q : A -> World -> Prop),
  {{ P }} @panic A v {{ Q }}.
Proof.
  intros. unfold hoare. intros w _.
  rewrite run_panic. exact I.
Qed.

(** ---- Types ---- *)
(** [GoAny] / [any] are defined up top (the panic semantics need them). *)

(** Signed integer types.
    [GoInt64] is [PrimInt63.int] — Rocq's primitive 63-bit machine integer —
    extracting to Go [int64], interpreted with SIGNED (Sint63) semantics.
    [+], [-], [*] are two's-complement, shared with the unsigned primitive and
    matching Go exactly; comparison and division use the signed Sint63
    operations.  So [2 - 5] is [-3] as in Go — not the unsigned reading
    [2^63 - 3].  HONEST LIMIT: Rocq's primitive int is 63-bit, so the model is
    faithful to int64 only within [-2^62, 2^62); the missing top bit (full
    int64 range and its overflow point) needs a Z-based model — see CLAUDE.md
    "Known gaps".  The remaining widths are axioms (no native Rocq equivalent). *)
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
From Stdlib Require Import Numbers.Cyclic.Int63.Sint63.
From Stdlib Require Import Floats.PrimFloat.
Notation GoFloat64 := float.
Axiom GoFloat32 : Type.

(** ---- Fixed-width unsigned integers (precise, computable models) ----

    A [uintN] value is carried by an [int] (PrimInt63) kept reduced mod 2^N by
    masking ([land .. (2^N-1)]) after EVERY operation.  That is EXACTLY Go's
    uintN arithmetic, which wraps mod 2^N.  Because the value always stays in
    [0, 2^N) (well below 2^62), the carrier never approaches the int63 boundary,
    signed and unsigned comparison agree, and the model is faithful to Go.

    These are DEFINITIONS, not axioms — so the model is computable ([vm_compute]
    discharges concrete wrap facts) and adds nothing to the trust base
    (consistency by construction).  The plugin recognises each op and lowers it
    to Go [int64] with the explicit mask, e.g. [u8_add a b] → [(a + b) & 0xff];
    the masked-int64 result is observationally identical to Go's [uint8] for the
    in-range values these ops produce.  (Type-level distinctness — forbidding the
    accidental mixing of a [uint8] with an [int] — is a separate safety layer to
    add later; this slice nails the *arithmetic* semantics first.) *)
Definition u8_lit (x : int) : int := PrimInt63.land x 255.
Definition u8_add (a b : int) : int := PrimInt63.land (PrimInt63.add a b) 255.
Definition u8_sub (a b : int) : int := PrimInt63.land (PrimInt63.sub a b) 255.
Definition u8_mul (a b : int) : int := PrimInt63.land (PrimInt63.mul a b) 255.
Definition u8_eqb (a b : int) : bool := PrimInt63.eqb a b.   (* in-range ⇒ exact *)
Definition u8_ltb (a b : int) : bool := PrimInt63.ltb a b.   (* in-range ⇒ unsigned = signed *)
Definition u8_leb (a b : int) : bool := PrimInt63.leb a b.

(** ---- Signed fixed-width integers ----

    [int8] in [-128, 128).  Go's int8 arithmetic wraps two's-complement.  Model:
    mask to 8 bits, then SIGN-EXTEND with [(m ^ 0x80) - 0x80] (flip the sign bit,
    subtract it), taking [m ∈ [0,256)] to [[-128,128)] — exactly what Go's
    [int8(x)] conversion does.  Comparison is SIGNED (values can be negative), so
    it uses [Sint63.ltb] → Go's signed int64 [<].  Computable and faithful; the
    plugin emits the explicit int64 mask + sign-extend, e.g.
    [i8_add a b] → [((((a + b) & 0xff) ^ 0x80) - 0x80)]. *)
Definition i8_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 255) 128) 128.
Definition i8_lit (x : int) : int := i8_norm x.
Definition i8_add (a b : int) : int := i8_norm (PrimInt63.add a b).
Definition i8_sub (a b : int) : int := i8_norm (PrimInt63.sub a b).
Definition i8_mul (a b : int) : int := i8_norm (PrimInt63.mul a b).
Definition i8_eqb (a b : int) : bool := PrimInt63.eqb a b.
Definition i8_ltb (a b : int) : bool := Sint63.ltb a b.   (* SIGNED comparison *)
Definition i8_leb (a b : int) : bool := Sint63.leb a b.

(** ---- Builtins ---- *)

Axiom print   : list GoAny -> IO unit.
Axiom println : list GoAny -> IO unit.

(** [panic], [bind_panic_l], [hoare_panic] are defined up top with the panic-
    aware semantics; [bind_panic_l] and [hoare_panic] are now proved lemmas. *)

(** ---- panic / recover semantics ----

    [catch m h] is the semantic of [defer func() { if r := recover(); r != nil { h(r) } }()].
    [recover()] in Go is just the panic value bound by [h] — it needs no separate axiom.

    Compound panics: if [h] itself panics with [w], [catch (panic v) h = h v = panic w],
    so the new panic [w] replaces [v].  This is correct Go semantics and falls out from
    [catch_panic] alone — no extra law needed.

    [with_defer] models [defer cleanup()] (without recover): runs [cleanup] on both
    normal exit and panic exit.  If [cleanup] panics mid-panic, the new panic wins —
    also correct Go semantics, again from [catch_panic] + [bind_panic_l]. *)

(** [catch] is declared up top; [catch_ret] and [catch_panic] are now proved
    lemmas (from [run_catch]), not axioms. *)

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

(** [defer_call f]: Go's [defer] keyword — schedule [f] to run when the
    enclosing *function* returns (LIFO across all defers, on both normal and
    panic exit), and continue immediately.  This is FUNCTION-scoped, unlike the
    block-scoped [with_defer]: deferred calls in a loop accumulate and all run
    at function return.  Lowers to [defer func(){ f }()] (Go provides the
    function-scoping, LIFO ordering, and run-at-return). *)
Axiom defer_call : IO unit -> IO unit.

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
    runtime type is already known.  Prefer [type_assert_safe] (below), the
    safe-by-construction default. *)
Axiom type_assert : forall {T : Type}, GoTypeTag T -> GoAny -> IO T.

Axiom type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (any x) = ret x.
(* type_assert panics if the runtime type does not match T.
   The precise failure law requires a decidable type equality; add when needed. *)

(** Safe checked assertion (the safe-by-construction default for [GoAny]).
    [type_assert_safe tag x (fun v ok => body)] lowers to Go's native two-value
    form [v, ok := x.(T); body]: when the runtime type matches [T], [ok = true]
    and [v = x]; otherwise [ok = false] and [v] is the zero value.  Because the
    caller must handle [ok = false], it cannot panic.  CPS like [recv_ok]. *)
Axiom type_assert_safe : forall {T B : Type},
  GoTypeTag T -> GoAny -> (T -> bool -> IO B) -> IO B.

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

(** ---- Maps via a heap in the world ----

    A Go map read observes the map's CURRENT (mutable) contents, so map reads are
    in [IO] (world-dependent).  The contents live in the world through an abstract
    heap interface: [map_sel k m w] is the value at key [k] of map [m] in world
    [w]; [map_upd] / [map_rem] are the world-updates that [map_set] / [map_delete]
    perform; [map_size] is the length.  These characterise a STANDARD heap, so
    they are satisfiable — hence CONSISTENT and non-degenerate — and the
    get-after-write laws below are THEOREMS derived from them, not asserted.

    Contrast the OLD model: [map_get_opt] was a PURE function of [m], which cannot
    reflect an IO write, so the get-after-write law was machine-checked DEGENERATE
    (it forced [map_set] never to succeed).  Making reads [IO] fixes that.
    Map access never panics: a missing key reads [None] (Go's zero value /
    [ok=false]); unlike slice indexing, which panics out of bounds. *)
Axiom map_sel  : forall {K V : Type}, K -> GoMap K V -> World -> option V.
Axiom map_upd  : forall {K V : Type}, K -> V -> GoMap K V -> World -> World.
Axiom map_rem  : forall {K V : Type}, K -> GoMap K V -> World -> World.
Axiom map_size : forall {K V : Type}, GoMap K V -> World -> GoInt.

Axiom map_get_opt : forall {K V : Type}, K -> GoMap K V -> IO (option V).
Axiom map_len     : forall {K V : Type}, GoMap K V -> IO GoInt.
(** [map_get_or k default m]: the value at [k], or [default] if absent.
    Extracts to [if v, ok := m[k]; ok { v } else { default }]. *)
Axiom map_get_or  : forall {K V : Type}, K -> V -> GoMap K V -> IO V.

Axiom map_set    : forall {K V : Type}, K -> V -> GoMap K V -> IO unit.
Axiom map_delete : forall {K V : Type}, K -> GoMap K V -> IO unit.

(** [run_io] equations: reads observe [map_sel]/[map_size] and leave the world
    unchanged; writes update it via [map_upd]/[map_rem] and return normally
    ([ORet] — so [map_set] is NOT forced to panic, unlike the old degenerate law). *)
Axiom run_map_get_opt : forall {K V} (k : K) (m : GoMap K V) (w : World),
  run_io (map_get_opt k m) w = ORet (map_sel k m w) w.
Axiom run_map_len : forall {K V} (m : GoMap K V) (w : World),
  run_io (map_len m) w = ORet (map_size m w) w.
Axiom run_map_get_or : forall {K V} (k : K) (default : V) (m : GoMap K V) (w : World),
  run_io (map_get_or k default m) w =
  ORet (match map_sel k m w with Some v => v | None => default end) w.
Axiom run_map_set : forall {K V} (k : K) (v : V) (m : GoMap K V) (w : World),
  run_io (map_set k v m) w = ORet tt (map_upd k v m w).
Axiom run_map_delete : forall {K V} (k : K) (m : GoMap K V) (w : World),
  run_io (map_delete k m) w = ORet tt (map_rem k m w).

(** Heap-interface laws — how [map_sel] reads after each update. *)
Axiom map_sel_upd_same : forall {K V} (k : K) (v : V) (m : GoMap K V) (w : World),
  map_sel k m (map_upd k v m w) = Some v.
Axiom map_sel_upd_diff : forall {K V} (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  k1 <> k2 -> map_sel k1 m (map_upd k2 v m w) = map_sel k1 m w.
Axiom map_sel_rem : forall {K V} (k : K) (m : GoMap K V) (w : World),
  map_sel k m (map_rem k m w) = None.
Axiom map_sel_empty : forall {K V} (k : K) (w : World),
  map_sel k (@map_empty K V) w = None.

(** GET-AFTER-WRITE laws — now THEOREMS, derived from the heap interface (these
    were a machine-checked-degenerate axiom under the old pure read). *)
Lemma map_get_set_same : forall {K V} (k : K) (v : V) (m : GoMap K V),
  bind (map_set k v m) (fun _ => map_get_opt k m) =
  bind (map_set k v m) (fun _ => ret (Some v)).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, !run_map_set. cbn.
  rewrite run_map_get_opt, map_sel_upd_same, run_ret. reflexivity.
Qed.

Lemma map_get_delete_same : forall {K V} (k : K) (m : GoMap K V),
  bind (map_delete k m) (fun _ => map_get_opt k m) =
  bind (map_delete k m) (fun _ => ret (@None V)).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, !run_map_delete. cbn.
  rewrite run_map_get_opt, map_sel_rem, run_ret. reflexivity.
Qed.

(** Reading the empty map gives [None]. *)
Lemma map_get_empty : forall {K V} (k : K),
  @map_get_opt K V k map_empty = ret None.
Proof.
  intros. apply run_io_inj. intro w.
  rewrite run_map_get_opt, map_sel_empty, run_ret. reflexivity.
Qed.

(** Setting key [k2] leaves the read at a different key [k1] unchanged (the value
    it had before the write, in the post-write world). *)
Lemma map_get_set_diff : forall {K V} (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  k1 <> k2 ->
  run_io (bind (map_set k2 v m) (fun _ => map_get_opt k1 m)) w =
  ORet (map_sel k1 m w) (map_upd k2 v m w).
Proof.
  intros K V k1 k2 v m w Hne.
  rewrite run_bind, run_map_set. cbn.
  rewrite run_map_get_opt, map_sel_upd_diff by exact Hne. reflexivity.
Qed.

(** [map_get_or] hits the stored value when present, falls back when absent. *)
Lemma map_get_or_hit : forall {K V} (k : K) (v default : V) (m : GoMap K V) (w : World),
  map_sel k m w = Some v -> run_io (map_get_or k default m) w = ORet v w.
Proof. intros K V k v default m w H. rewrite run_map_get_or, H. reflexivity. Qed.
Lemma map_get_or_miss : forall {K V} (k : K) (default : V) (m : GoMap K V) (w : World),
  map_sel k m w = None -> run_io (map_get_or k default m) w = ORet default w.
Proof. intros K V k default m w H. rewrite run_map_get_or, H. reflexivity. Qed.

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

(** ---- Channels via state in the world (the concurrent denotational model) ----

    Channel semantics rest on STATE, not on bind-sequencing intuition.  Each
    channel has, in the world, a FIFO [chan_buf] (values sent but not yet
    received; head = next to receive) and a [chan_closed] flag.  Sends/receives/
    closes are world-updates ([chan_send_upd] enqueues, [chan_recv_upd] dequeues
    the head, [chan_close_upd] marks closed).  This MIRRORS the map heap model:
    the interface characterises a standard FIFO + flag, hence is satisfiable
    (consistent, non-degenerate), and the channel LAWS below are now THEOREMS
    derived from it — not free-standing axioms asserted on intuition.

    BLOCKING is idealised away (like divergence / OOM, and matching [run_io]'s
    totality): a [recv] equation is given only when the buffer is non-empty (or
    the channel is closed); a [recv] on a permanently-empty open channel blocks
    forever, which has no denotation here — a deadlock, out of scope.  This is the
    SEQUENTIAL (single-goroutine, or correctly-synchronised) slice; the
    cross-goroutine HAPPENS-BEFORE partial order is the next layer. *)
Axiom chan_buf    : forall {A : Type}, GoChan A -> World -> list A.
Axiom chan_closed : forall {A : Type}, GoChan A -> World -> bool.
Axiom chan_send_upd  : forall {A : Type}, GoChan A -> A -> World -> World.
Axiom chan_recv_upd  : forall {A : Type}, GoChan A -> World -> World.
Axiom chan_close_upd : forall {A : Type}, GoChan A -> World -> World.

(** Heap-interface laws: how [chan_buf]/[chan_closed] read after each update. *)
Axiom chan_buf_send : forall {A} (ch : GoChan A) (v : A) (w : World),
  chan_buf ch (chan_send_upd ch v w) = chan_buf ch w ++ (v :: nil).   (* enqueue at tail *)
Axiom chan_buf_recv : forall {A} (ch : GoChan A) (v : A) (rest : list A) (w : World),
  chan_buf ch w = v :: rest -> chan_buf ch (chan_recv_upd ch w) = rest.  (* dequeue head *)
Axiom chan_closed_send : forall {A} (ch : GoChan A) (v : A) (w : World),
  chan_closed ch (chan_send_upd ch v w) = chan_closed ch w.
Axiom chan_closed_recv : forall {A} (ch : GoChan A) (w : World),
  chan_closed ch (chan_recv_upd ch w) = chan_closed ch w.
Axiom chan_closed_close : forall {A} (ch : GoChan A) (w : World),
  chan_closed ch (chan_close_upd ch w) = true.

(** [run_io] equations — conditioned on channel state.  A send on an OPEN channel
    enqueues and returns; on a CLOSED channel it panics (Go spec).  A receive,
    when the buffer has a head, reads it and dequeues; when the buffer is empty
    and the channel is closed, [recv_ok] yields [(zero, false)].  Close marks the
    channel closed; a double close panics. *)
Axiom run_send : forall {A} (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false ->
  run_io (send ch v) w = ORet tt (chan_send_upd ch v w).
Axiom run_send_closed : forall {A} (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = true ->
  run_io (send ch v) w = OPanic (any tt) w.
Axiom run_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (rest : list A) (w : World),
  chan_buf ch w = v :: rest ->
  run_io (recv tag ch) w = ORet v (chan_recv_upd ch w).
Axiom run_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (v : A) (rest : list A) (w : World),
  chan_buf ch w = v :: rest ->
  run_io (recv_ok tag ch f) w = run_io (f v true) (chan_recv_upd ch w).
Axiom run_recv_ok_closed_empty : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (w : World),
  chan_buf ch w = nil -> chan_closed ch w = true ->
  run_io (recv_ok tag ch f) w = run_io (f (zero_val tag) false) w.
Axiom run_close : forall {A} (ch : GoChan A) (w : World),
  chan_closed ch w = false ->
  run_io (close_chan ch) w = ORet tt (chan_close_upd ch w).
Axiom run_close_closed : forall {A} (ch : GoChan A) (w : World),
  chan_closed ch w = true ->
  run_io (close_chan ch) w = OPanic (any tt) w.

(** ---- The channel laws, now DERIVED as theorems ---- *)

(** After [send ch v] into an OPEN, EMPTY channel, the next [recv] returns [v].
    (Honest conditions the old unconditional axiom hid: send must not panic on a
    closed channel, and FIFO means [recv] returns [v] only when [v] is at the
    head — i.e. the buffer was empty before the send.) *)
Theorem send_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false -> chan_buf ch w = nil ->
  run_io (bind (send ch v) (fun _ => recv tag ch)) w
  = ORet v (chan_recv_upd ch (chan_send_upd ch v w)).
Proof.
  intros A tag ch v w Hclosed Hempty.
  rewrite run_bind, (run_send ch v w Hclosed). cbn.
  apply (run_recv tag ch v nil).
  rewrite chan_buf_send, Hempty. reflexivity.
Qed.

(** [recv_ok] variant: after [send ch v] into an open, empty channel, [recv_ok]
    delivers [(v, true)] and runs the continuation in the dequeued world. *)
Theorem send_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A)
    (f : A -> bool -> IO B) (w : World),
  chan_closed ch w = false -> chan_buf ch w = nil ->
  run_io (bind (send ch v) (fun _ => recv_ok tag ch f)) w
  = run_io (f v true) (chan_recv_upd ch (chan_send_upd ch v w)).
Proof.
  intros A B tag ch v f w Hclosed Hempty.
  rewrite run_bind, (run_send ch v w Hclosed). cbn.
  apply (run_recv_ok tag ch f v nil).
  rewrite chan_buf_send, Hempty. reflexivity.
Qed.

(** Sending on a closed channel panics (Go spec): close then send → panic. *)
Theorem send_closed_panics : forall {A} (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false ->
  run_io (bind (close_chan ch) (fun _ => send ch v)) w
  = OPanic (any tt) (chan_close_upd ch w).
Proof.
  intros A ch v w Hopen.
  rewrite run_bind, (run_close ch w Hopen). cbn.
  exact (run_send_closed ch v (chan_close_upd ch w) (chan_closed_close ch w)).
Qed.

(** Closing an already-closed channel panics (Go spec): close then close → panic. *)
Theorem double_close_panics : forall {A} (ch : GoChan A) (w : World),
  chan_closed ch w = false ->
  run_io (bind (close_chan ch) (fun _ => close_chan ch)) w
  = OPanic (any tt) (chan_close_upd ch w).
Proof.
  intros A ch w Hopen.
  rewrite run_bind, (run_close ch w Hopen). cbn.
  exact (run_close_closed ch (chan_close_upd ch w) (chan_closed_close ch w)).
Qed.

(** [recv_ok] on a closed, EMPTY channel returns [(zero_val tag, false)] — Go's
    "receive from a closed channel" rule.  This could NOT be an unconditional
    axiom (with [send_recv_ok] it forces [v = zero_val tag] for all [v], an
    inconsistency); conditioning on the channel state makes it sound. *)
Theorem recv_ok_closed_empty : forall {A B} (tag : GoTypeTag A) (ch : GoChan A)
    (f : A -> bool -> IO B) (w : World),
  chan_buf ch w = nil -> chan_closed ch w = true ->
  run_io (recv_ok tag ch f) w = run_io (f (zero_val tag) false) w.
Proof. intros. apply run_recv_ok_closed_empty; assumption. Qed.

(** ---- Happens-before: the partial order on channel events (go.dev/ref/mem) ----

    Phase 2 of the concurrency model.  Phase 1 (above) grounded the channel LAWS
    in buffer state; this grounds the ORDERING that race/deadlock-freedom rest on.
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

    Scope: this is one channel's event order.  Tying events to the [run_io] world
    operations and to heap accesses (cross-goroutine visibility + a data-race
    definition) is Phase 3. *)
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

(** ---- Phase 3: data races, and channel synchronisation that prevents them ----

    A DATA RACE (go.dev/ref/mem) is two accesses to the SAME memory location, at
    least one a WRITE, UNORDERED by happens-before.  With the [hb] order in hand
    this is finally STATABLE.  The generic guarantee is that happens-before
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
    in each goroutine, plus the Phase-2 channel rule [mp_sync] (send synchronised
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
    happens-before ordered.  This is what the package-import and library-boundary
    layers discharge — for imported modules by composing each module's ordering;
    at a library boundary by an exclusive-ownership window (next steps).  The
    message-passing program is the first instance: whole-program race-free. *)
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
    false], this form cannot panic out of bounds.  [i : int] is SIGNED (Sint63),
    so the check covers BOTH ends ([0 <= i < len]); a negative index is in range
    for Go's panic, so it must yield [ok = false], not slip through. *)
Axiom slice_at_ok : forall {A B : Type},
  GoTypeTag A -> GoSlice A -> int -> (A -> bool -> IO B) -> IO B.

(** ---- Mutable local variables ----

    [Ref A] is a mutable cell holding an [A] — Go's mutable local variable.
    Pure [let]-binding is single-assignment and cannot express a value that
    *changes* (a loop counter, an accumulator updated in place); a [Ref] can.
    [ref_new v] declares the variable ([x := v]); [ref_get] reads it; [ref_set]
    assigns ([x = v]).  A local cell extracts to a plain Go variable;
    cross-function sharing (pointers, [*T]) is a later, separate step. *)
Axiom Ref     : Type -> Type.
Axiom ref_new : forall {A : Type}, A -> IO (Ref A).
(* [ref_get] carries a [GoTypeTag] so that, when a read is bound inside a loop
   block, the lowering knows the Go type to hoist its declaration ([var x T])
   to a point that dominates the uses (assigning with [=], not [:=]). *)
Axiom ref_get : forall {A : Type}, GoTypeTag A -> Ref A -> IO A.
Axiom ref_set : forall {A : Type}, Ref A -> A -> IO unit.

(** A [Ref]'s value lives in the world (same heap discipline as maps): [ref_sel]
    is the current value, [ref_upd] the [ref_set] update.  [ref_get] is already
    [IO], so this needs NO extraction change — it only grounds the read-after-
    write law below as a THEOREM (refs had no laws before). *)
Axiom ref_sel : forall {A : Type}, Ref A -> World -> A.
Axiom ref_upd : forall {A : Type}, Ref A -> A -> World -> World.
Axiom run_ref_get : forall {A} (tag : GoTypeTag A) (r : Ref A) (w : World),
  run_io (ref_get tag r) w = ORet (ref_sel r w) w.
Axiom run_ref_set : forall {A} (r : Ref A) (v : A) (w : World),
  run_io (ref_set r v) w = ORet tt (ref_upd r v w).
Axiom ref_sel_upd_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel r (ref_upd r v w) = v.

(** Read-after-write — a THEOREM: after [ref_set r v], [ref_get] returns [v]. *)
Lemma ref_get_set_same : forall {A} (tag : GoTypeTag A) (r : Ref A) (v : A),
  bind (ref_set r v) (fun _ => ref_get tag r) =
  bind (ref_set r v) (fun _ => ret v).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, !run_ref_set. cbn.
  rewrite run_ref_get, ref_sel_upd_same, run_ret. reflexivity.
Qed.

(** ---- Bounded iteration (loops, step 8) ----

    [for_each xs body] runs [body] on each element of [xs], in order.  It is a
    total Fixpoint (structural recursion on the slice), so it always terminates
    and its unfolding is a provable equation:
      [for_each nil body = ret tt]
      [for_each (x :: rest) body = body x >>' for_each rest body]
    The plugin lowers a call to a Go [for _, x := range xs { body }] loop
    rather than to recursion, so there is no unbounded stack and the generated
    code is idiomatic.  (Unbounded [for]/[for cond] loops, which need a
    non-terminating combinator, come separately.) *)
Fixpoint for_each {A : Type} (xs : GoSlice A) (body : A -> IO unit) : IO unit :=
  match xs with
  | nil        => ret tt
  | cons x rest => bind (body x) (fun _ => for_each rest body)
  end.

(** [slice_fold xs init step] is a pure left fold: it threads an accumulator
    through the slice, [step]ping it with each element.  A total Fixpoint, so
    its unfolding is provable:
      [slice_fold nil init step = init]
      [slice_fold (x :: rest) init step = slice_fold rest (step init x) step]
    The plugin lowers a [let acc := slice_fold xs init step in …] to an
    accumulator loop:
      [acc := init; for _, x := range xs { acc = step acc x }; …]
    so e.g. summing a slice is a real Go [for] loop, and "the running sum does
    not overflow" is provable on the model (see [add_no_overflow_exact]). *)
Fixpoint slice_fold {A S : Type} (xs : GoSlice A) (init : S) (step : S -> A -> S) : S :=
  match xs with
  | nil        => init
  | cons x rest => slice_fold rest (step init x) step
  end.

(** ---- Control flow as a CFG (the goto model) ----

    Every Go control construct is, underneath, a control-flow graph of basic
    blocks joined by gotos.  We model that directly and completely: a function
    body is a set of labelled blocks; each block runs its IO effects then
    transfers control — [Jump n] (goto block n) or [Done] (return).  Any Go
    control flow, structured or irreducible, is a CFG, so this is complete and
    [goto] is the native edge.

    [run_blocks start body]: start at label [start]; run [body l] (which does IO
    and yields a [Next]); follow [Jump]s until [Done].  It lives in [IO] because
    a backward [Jump] need not terminate.  The plugin does NOT emit a dispatch
    loop — it emits the blocks as Go labels + [goto], and a structuring pass
    lifts reducible graphs back to [if]/[for]/[break].  Structured combinators
    (if, for_each, slice_fold) are patterns that pass recognises, not the model. *)
Inductive Next : Type :=
  | Jump : nat -> Next   (* goto block n *)
  | Done : Next.         (* return from the function *)

(** [run_blocks start blocks]: the blocks are given as a list (block [n] is the
    nth entry); start at [start], run each block (IO ending in a [Next]), follow
    [Jump]s until [Done].  In [IO] because a backward [Jump] need not terminate.
    The plugin emits the blocks as Go labels + [goto] (only labels that are
    [Jump] targets are emitted, since Go rejects unused labels). *)
Axiom run_blocks : nat -> list (IO Next) -> IO unit.

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

(** ---- Linear sessions via an indexed monad ----

    An earlier CPS endpoint API ([SessEndpoint P], [sess_send ep v k], …)
    enforced the protocol ORDER but not LINEARITY: it handed the continuation
    the advanced endpoint while leaving the ORIGINAL [ep] in scope, and Rocq is
    not substructural, so a double-send (or a silent mid-protocol abandonment)
    type-checked.  Ordering was enforced; exactly-once use was not.

    This indexed (parameterised) monad fixes it by putting the protocol state in
    the TYPE INDEX, not in a reusable value.  [Sess i j A] is a session fragment
    that advances the protocol from state [i] to state [j], yielding [A].  There
    is no endpoint value to reuse; operations consume the head step of the index
    and [sbind] threads the state; and a *runnable* session must thread from the
    full protocol [P] all the way to [PEnd] ([Sess P PEnd unit]).  Hence
    double-use, wrong order/direction/payload, AND incomplete protocols are all
    Rocq TYPE ERRORS (see the [Fail] tests in main.v). *)

Axiom Sess : Proto -> Proto -> Type -> Type.

(** Pure value; protocol state unchanged.  Lowers like [ret]. *)
Axiom sret : forall {P : Proto} {A : Type}, A -> Sess P P A.

(** Sequence: [m] advances [i→j], then [k a] advances [j→k].  Lowers like
    [bind] (sequential Go statements). *)
Axiom sbind : forall {P Q R : Proto} {A B : Type},
  Sess P Q A -> (A -> Sess Q R B) -> Sess P R B.

(** Send: consumes the head [PSend A] step.  No endpoint argument — the channel
    is implicit, supplied by the enclosing [run_session].
    Lowers to [_sess_ch <- any(v)]. *)
Axiom ssend : forall {A : Type} {P : Proto}, A -> Sess (PSend A P) P unit.

(** Receive: consumes the head [PRecv A] step, yielding the received value.
    Lowers to [_r := <-_sess_ch; _r.(T)]. *)
Axiom srecv : forall {A : Type} {P : Proto}, GoTypeTag A -> Sess (PRecv A P) P A.

(** Lift an [IO] action into a session at any protocol state (consumes no
    protocol step) — e.g. to print a received value.  Lowers to the IO body. *)
Axiom slift : forall {P : Proto} {A : Type}, IO A -> Sess P P A.

(** Run two complementary roles concurrently: the client realises [P] to
    completion, the server realises [dual P].  Allocates one shared channel,
    spawns the server, runs the client.
    Lowers to: [_sess_ch := make(chan any); go func(){ <server> }(); <client>]. *)
Axiom run_session : forall {P : Proto},
  Sess P PEnd unit -> Sess (dual P) PEnd unit -> IO unit.
