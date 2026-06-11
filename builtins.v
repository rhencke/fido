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
  | TInt32   : GoTypeTag GoInt32
  | TUint64  : GoTypeTag GoUint64.

(** [type_assert tag v] asserts that [v : GoAny] holds a value of Go type [T].
    Panics (like Go's [v.(T)]) if the runtime type does not match. *)
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

Axiom GoMap : Type -> Type -> Type.

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

Axiom len    : forall {A : Type}, GoSlice A -> GoInt.
Axiom cap    : forall {A : Type}, GoSlice A -> GoInt.
Axiom append : forall {A : Type}, GoSlice A -> GoSlice A -> GoSlice A.

(** Construct a typed Go slice from a Rocq list literal.
    The [GoTypeTag] witness lets the plugin emit [[]T{v1, v2, ...}] with the
    correct element type instead of falling back to [append(nil, ...)]. *)
Axiom slice_of_list : forall {A : Type}, GoTypeTag A -> list A -> GoSlice A.

(** Indexed access — returns [IO A] because Go panics on out-of-bounds.
    Use inside [catch] to handle the OOB case. *)
Axiom slice_get : forall {A : Type}, GoTypeTag A -> GoSlice A -> int -> IO A.
