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
From Stdlib Require Import Floats.PrimFloat.
Notation GoFloat64 := float.
Axiom GoFloat32 : Type.

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
