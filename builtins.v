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
From Stdlib Require Import ZArith.   (* Z.to_nat for the slice index *)
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.   (* [int] — hoisted so the numeric
   carrier types can be DEFINED as [int] (they only appear in tags, never in Go). *)
From Stdlib Require Import Floats.PrimFloat.          (* [float] — for [GoFloat32] *)

(** ---- IO monad ----

    [IO A] represents a Go effectful computation.  The type and its
    combinators are CONCRETE definitions ([IO A := World -> Outcome A]) that the
    extraction plugin lowers BY NAME — [bind m f] to sequential Go statements,
    [ret x] to its argument — erasing the world token in the generated code.

    For PROOFS we add a denotational semantics: [run_io m w] gives the
    concrete meaning of [m] as a function from the current world [w] to a
    result and updated world.  [run_io] is a proof-only device; it is never
    extracted.  From [run_ret], [run_bind], and [run_io_inj] the monad laws
    are provable lemmas rather than postulated axioms.

    The Hoare triple [{{ P }} m {{ Q }}] is defined via [run_io], giving us a
    pre/postcondition framework for program verification.  This is the
    foundation on which channel session-type proofs will be built. *)

(** ---- World, [GoAny], outcomes, and the IO monad — a CONCRETE proof-only model. ----

    [World] is still abstract HERE; it becomes a concrete record once channels/refs/
    maps are concretised (it cannot go concrete alone — that would make their laws,
    e.g. [chan_buf_send], inconsistent).  But [IO A := World -> Outcome A] makes the
    monad and its [run_*] laws DEFINITIONS / THEOREMS rather than axioms.  Extraction
    never sees these bodies: the plugin lowers [ret]/[bind]/[panic]/[catch] BY NAME to
    sequential Go and erases the world token.

    [run_io m w] is the meaning of [m] from world [w] as an OUTCOME: [ORet a w']
    (normal completion) or [OPanic v w'] (panicked with [v]).  Panic as an OUTCOME —
    not a total [A * World] — is essential: with the old total type the law "[panic]
    satisfies every postcondition" forced [World] empty ([World -> False]), collapsing
    the layer.  DIVERGENCE is idealised away: [run_io] is total (terminates). *)

(** Signed integer types.
    [GoInt64] is [PrimInt63.int] — Rocq's primitive 63-bit machine integer —
    extracting to Go [int64], interpreted with SIGNED (Sint63) semantics.
    [+], [-], [*] are two's-complement, shared with the unsigned primitive and
    matching Go exactly; comparison and division use the signed Sint63
    operations.  So [2 - 5] is [-3] as in Go — not the unsigned reading
    [2^63 - 3].  HONEST LIMIT: Rocq's primitive int is 63-bit, so the model is
    faithful to int64 only within [-2^62, 2^62); the missing top bit (full
    int64 range and its overflow point) needs a Z-based model — see CLAUDE.md
    "Known gaps".  The remaining widths are DEFINED as [int] (placeholders for the
    faithful fixed-width records below — the carriers exist only for the tag index). *)
(** These are OPAQUE CARRIER types that appear ONLY inside [GoTypeTag] constructors
    (e.g. [TInt : GoTypeTag GoInt]) — never as a value in extracted Go — so defining
    them costs nothing observable.  They are PLACEHOLDERS: the FAITHFUL fixed-width
    models are the [GoU8]/[GoI8]/… records below; these carriers exist for the tag's
    index.  Defined as [int] just to retire the axioms. *)
Definition GoInt   : Type := int.   (* int    — platform-width, typically 64-bit *)
Definition GoInt8  : Type := int.   (* int8   — 8-bit  *)
Definition GoInt16 : Type := int.   (* int16  — 16-bit *)
Definition GoInt32 : Type := int.   (* int32  — 32-bit *)
(* GoInt64 = PrimInt63.int, loaded separately via Stdlib *)
Notation GoRune := GoInt32.  (* rune is an alias for int32 *)

(** Unsigned integer types. *)
Definition GoUint   : Type := int.   (* uint    — platform-width *)
Definition GoUint8  : Type := int.   (* uint8   — 8-bit  *)
Definition GoUint16 : Type := int.   (* uint16  — 16-bit *)
Definition GoUint32 : Type := int.   (* uint32  — 32-bit *)
Definition GoUint64 : Type := int.   (* uint64  — 64-bit *)
(* [GoByte] (Go's [byte] = an alias for [uint8]) is bound after [GoU8] below, to
   the FAITHFUL [GoU8] record rather than the opaque [GoUint8] axiom. *)

(** Go's string type (Go spec "String types"): "a string value is a (possibly
    empty) sequence of BYTES; ... strings are immutable".  Modelled as Coq's
    [string] (Strings.String) — itself a sequence of [Ascii.ascii], i.e. a byte
    sequence — so [len] is the BYTE count and [s[i]] is the i'th BYTE (a [byte] =
    [uint8]), exactly as the spec defines.  Immutability is automatic (a pure
    value).  The plugin maps [string] → Go [string] and decodes a [String]/
    [Ascii]/[EmptyString] literal to a byte-faithful Go string literal (Go
    escaping).
    (The earlier [list GoRune] model was the RUNE view — how [range s] iterates,
    NOT how Go indexes — so it mismodelled [len]/[s[i]]; the rune view is a
    separate UTF-8 decode, deferred.) *)
From Stdlib Require Import Strings.String Strings.Ascii.
Definition GoString : Type := string.

(** Go's slice type — a resizable sequence of elements.
    Modelled as [list A] so Rocq's list theory applies directly.
    The plugin maps [list A] → [[]T] for any element type [A] (so a rune slice
    [list GoRune] is Go's [[]int32]; the byte-sequence [string] is separate —
    see [GoString] above).

    NOTE — aliasing: like maps, slices are reference types in Go.  The pure
    functional model (append returning a new list) is safe for single-goroutine
    sequential programs where there is no aliasing of the underlying array.
    For concurrent programs or programs that intentionally alias slice headers,
    [append] should be moved to [IO] (same reasoning as [map_set]/[map_delete]). *)
Definition GoSlice (A : Type) : Type := list A.

(** Floating-point types.
    [GoFloat64] is Rocq's primitive [PrimFloat.float] — IEEE 754 double
    precision, with verified arithmetic semantics in the kernel.
    [GoFloat32] is DEFINED as [float] (Rocq has no native 32-bit float; faithful
    32-bit rounding is a tracked gap — see below). *)
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.
From Stdlib Require Import Numbers.Cyclic.Int63.Sint63.
From Stdlib Require Import Floats.PrimFloat.
(* [BinInt] gives [Z] for the FULL-WIDTH [GoI64] model below (the 63-bit primitive
   [int] is one bit short of int64).  Required WITHOUT [Open Scope Z_scope] so the
   existing [%uint63]/[%sint63] defaults are untouched — all [Z] use is qualified
   ([Z.add]/[Z.modulo]/…) with explicit [%Z] literals. *)
From Stdlib Require Import BinInt.
Notation GoFloat64 := float.
(** [GoFloat32] has no native Rocq float32 (holdout #1 in ZERO_AXIOMS_PLAN.md).  Modelled
    here as [float] (= float64): a CRUDE idealisation — no float32 op is modelled and no
    law mentions it, and the carrier appears only in [TFloat32], never as an extracted
    value — so this retires the axiom; faithful 32-bit rounding is deferred. *)
Definition GoFloat32 : Type := float.

(** [GoChan]/[GoMap] are CONCRETE phantom-LOCATION records (no longer axioms): a
    [GoChan A] is a handle [{ ch_loc : int }] into the world's channel state, the
    element type [A] carried only PHANTOM (in the type, never as a field).  They do
    NOT carry their [GoTypeTag] — that would make [GoTypeTag] (which references them
    via [TChan]/[TMap]) UNIVERSE-INCONSISTENT (a tag indexing over a type that
    stores a tag).  Keeping them tag-free breaks the cycle, so [GoTypeTag] below can
    reference them freely.  At extraction [GoChan A] → Go [chan T], [GoMap K V] →
    [map[K]V] (the plugin renders by type NAME); the [ch_loc]/[gm_loc] handle and
    the record wrapper are erased.  (Channel/map STATE ops are DEFINITIONS over
    these concrete handles.) *)
Record GoChan (A : Type) : Type := MkChan { ch_loc : int }.
Record GoMap  (K V : Type) : Type := MkMap { gm_loc : int }.
Arguments MkChan {A} _.
Arguments ch_loc {A} _.
Arguments MkMap {K V} _.
Arguments gm_loc {K V} _.

(** ---- Type assertions ----

    [GoTypeTag T] is a term-level witness encoding the Go type [T].
    Because it is an inductive (not a type), it survives extraction —
    the plugin inspects the constructor to emit [v.(T)] with the right type.

    Extend this inductive as new Go types are added to builtins. *)

(* Numeric-wrapper records, hoisted ABOVE GoTypeTag so TU8../TUnit can index them. *)
Record GoU8 := MkU8 { u8raw : int }.
Record GoI8 := MkI8 { i8raw : int }.
Record GoU16 := MkU16 { u16raw : int }.
Record GoI16 := MkI16 { i16raw : int }.
Record GoU32 := MkU32 { u32raw : int }.
Record GoI32 := MkI32 { i32raw : int }.
(* FULL-WIDTH signed int64 (Go spec "Numeric types": [int64] is the set of all
   signed 64-bit integers).  Carried by [Z] — NOT the 63-bit [int] — so the model
   is faithful across the WHOLE int64 range and wraps at the true [2^63], unlike
   the [Sint63] [int] carrier (faithful only within [-2^62, 2^62)).  The wrapper
   ERASES at extraction (like [GoU8]); a [GoI64] value is a Go [int64], which wraps
   natively at [2^64], so the emitted ops need no mask. *)
Record GoI64 := MkI64 { i64raw : Z }.

Inductive GoTypeTag : Type -> Type :=
  | TBool    : GoTypeTag bool
  | TInt64   : GoTypeTag int             (* → int64 *)
  | TFloat64 : GoTypeTag float            (* → float64 *)
  | TString  : GoTypeTag GoString
  | TU8  : GoTypeTag GoU8  | TI8  : GoTypeTag GoI8
  | TU16 : GoTypeTag GoU16 | TI16 : GoTypeTag GoI16
  | TU32 : GoTypeTag GoU32 | TI32 : GoTypeTag GoI32
  | TI64 : GoTypeTag GoI64               (* → int64 (full-width Z-carried) *)
  | TUnit : GoTypeTag unit
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

(** TRANSPARENT congruences for the now-CONCRETE [GoChan]/[GoMap] records, forced
    to live at [@eq Type].  Two reasons they are not the stdlib [f_equal]/[f_equal2]:
    (1) [f_equal2] is [Qed] (opaque) so [f_equal2 GoMap eq_refl eq_refl] does NOT
    reduce to [eq_refl], breaking [tag_eq_refl]; (2) since [GoChan A]/[GoMap K V] are
    records over [int : Set] they land in [Set], so a bare [f_equal GoChan] yields an
    [@eq Set] proof — but [tag_eq]'s result [option (A = B)] is at [@eq Type] (the
    [GoTypeTag] index universe).  Annotating the return as [@eq Type] (valid by
    cumulativity, [Set ⊆ Type]) produces a proof at the right universe, and the
    direct dependent match reduces on [eq_refl]. *)
Definition gochan_cong {A A'} (p : A = A') : @eq Type (GoChan A) (GoChan A') :=
  match p in (_ = X) return (@eq Type (GoChan A) (GoChan X)) with eq_refl => eq_refl end.
Definition gomap_cong {K K' V V'} (p : K = K') (q : V = V')
  : @eq Type (GoMap K V) (GoMap K' V') :=
  match p in (_ = K2), q in (_ = V2) return (@eq Type (GoMap K V) (GoMap K2 V2)) with
  | eq_refl, eq_refl => eq_refl
  end.

(** Decidable tag equality WITH type recovery: if two tags are the same, hand back a
    proof that their indexed types are equal (so a heterogeneous heap can cast a stored
    value to the accessor's type).  Provable because [GoTypeTag] is a finite inductive —
    the foundation for the concrete typed heap and for [type_assert].  (Same-constructor
    matching suffices: a cell is read with the tag it was written with.) *)
Fixpoint tag_eq {A B} (ta : GoTypeTag A) (tb : GoTypeTag B) {struct ta} : option (A = B) :=
  match ta in GoTypeTag A', tb in GoTypeTag B' return option (A' = B') with
  | TBool, TBool       => Some eq_refl
  | TInt64, TInt64     => Some eq_refl
  | TFloat64, TFloat64 => Some eq_refl
  | TString, TString   => Some eq_refl
  | TU8, TU8   => Some eq_refl | TI8, TI8   => Some eq_refl
  | TU16, TU16 => Some eq_refl | TI16, TI16 => Some eq_refl
  | TU32, TU32 => Some eq_refl | TI32, TI32 => Some eq_refl
  | TI64, TI64 => Some eq_refl
  | TUnit, TUnit => Some eq_refl
  | TInt, TInt         => Some eq_refl
  | TInt8, TInt8       => Some eq_refl
  | TInt16, TInt16     => Some eq_refl
  | TInt32, TInt32     => Some eq_refl
  | TUint, TUint       => Some eq_refl
  | TUint8, TUint8     => Some eq_refl
  | TUint16, TUint16   => Some eq_refl
  | TUint32, TUint32   => Some eq_refl
  | TUint64, TUint64   => Some eq_refl
  | TFloat32, TFloat32 => Some eq_refl
  | TChan a, TChan b   => match tag_eq a b with Some p => Some (gochan_cong p) | None => None end
  | TSlice a, TSlice b => match tag_eq a b with Some p => Some (f_equal GoSlice p) | None => None end
  | TMap ka va, TMap kb vb =>
      match tag_eq ka kb, tag_eq va vb with
      | Some p, Some q => Some (gomap_cong p q)
      | _, _ => None
      end
  | _, _ => None
  end.

(** Cast a value along a tag match (identity when the tags agree). *)
Definition tag_coerce {A B} (ta : GoTypeTag A) (tb : GoTypeTag B) (x : B) : option A :=
  match tag_eq ta tb with Some p => Some (eq_rect B (fun T => T) x A (eq_sym p)) | None => None end.

(** A tag is equal to itself ([Some eq_refl]) — by induction on the finite tag
    inductive.  The foundation for the typed-heap read-after-write laws: a cell is
    read with the SAME tag it was written with, so the coercion is the identity. *)
Lemma tag_eq_refl : forall {A} (t : GoTypeTag A), tag_eq t t = Some eq_refl.
Proof.
  induction t; cbn; try reflexivity.
  - rewrite IHt; reflexivity.                       (* TChan *)
  - rewrite IHt; reflexivity.                       (* TSlice *)
  - rewrite IHt1, IHt2; reflexivity.                (* TMap (gomap_cong reduces) *)
Qed.

(** [tag_coerce t t x = Some x]: coercing along a tag's reflexive match is the
    identity (from [tag_eq_refl]). *)
Lemma tag_coerce_refl : forall {A} (t : GoTypeTag A) (x : A), tag_coerce t t x = Some x.
Proof. intros A t x. unfold tag_coerce. rewrite tag_eq_refl. reflexivity. Qed.

(** Every Go type has a zero value (false, 0, 0.0, nil, "", …) — its [GoTypeTag]
    determines which.  Now a DEFINITION (not an axiom): a recursion on the tag that
    is total precisely because [GoTypeTag] enumerates exactly the Go types and each
    has a concrete zero (the composite [GoChan]/[GoMap] zeros use the nil-location
    handle [MkChan 0]/[MkMap 0]; a slice's is [nil]).  The plugin lowers a
    [zero_val] CALL by name to the Go zero literal (0/false/""/nil), so this body
    affects only proofs, never the emitted Go.  (The default for a [recv] from an
    empty/closed channel, an out-of-range index, etc.) *)
Definition zero_val {A : Type} (t : GoTypeTag A) : A :=
  match t in GoTypeTag A' return A' with
  | TBool    => false
  | TInt64   => 0%uint63
  | TFloat64 => 0%float
  | TString  => EmptyString
  | TU8  => MkU8 0%uint63  | TI8  => MkI8 0%uint63
  | TU16 => MkU16 0%uint63 | TI16 => MkI16 0%uint63
  | TU32 => MkU32 0%uint63 | TI32 => MkI32 0%uint63
  | TI64 => MkI64 0%Z
  | TUnit => tt
  | TInt     => 0%uint63
  | TInt8    => 0%uint63
  | TInt16   => 0%uint63
  | TInt32   => 0%uint63
  | TUint    => 0%uint63
  | TUint8   => 0%uint63
  | TUint16  => 0%uint63
  | TUint32  => 0%uint63
  | TUint64  => 0%uint63
  | TFloat32 => 0%float
  | TChan _  => MkChan 0%uint63       (* nil channel (handle erased; plugin emits nil) *)
  | TSlice _ => nil                   (* empty slice *)
  | TMap _ _ => MkMap 0%uint63        (* nil map *)
  end.

(** ---- [GoAny] / [any] — Go's [interface{}], now a TAGGED (type, value) pair ----

    Go's [interface{}] carries its value's DYNAMIC TYPE at runtime, which is exactly
    what a type assertion [v.(T)] inspects.  So [GoAny] is a [{A & GoTypeTag A * A}]:
    the value [A] PLUS its runtime [GoTypeTag].  (It must be DEFINED here, after
    [GoTypeTag] — and [GoTypeTag] no longer has a [TAny] constructor, because a tagged
    [GoAny] referenced by [TAny : GoTypeTag GoAny] is UNIVERSE-INCONSISTENT, the same
    wall as a tag-carrying [GoChan].  This is sound: a value's dynamic type is always a
    CONCRETE type — Go flattens nested interfaces — so [GoTypeTag GoAny] is never the
    actual runtime type of any value.  The only thing lost is "assert TO [any]" / typed
    [chan any]/[[]any] containers; tracked, fail-loud, not an axiom.)

    [Tagged A] is the typeclass that supplies the runtime tag, so the [any x] notation
    INFERS it (the existing [any x] sites are unchanged); [anyt tag x] gives it
    explicitly (for a generic value type, where no instance can be resolved). *)
Definition GoAny : Type := { A : Type & (A * GoTypeTag A)%type }.
Class Tagged (A : Type) : Type := the_tag : GoTypeTag A.
Arguments the_tag A {_}.
(* [anyt] stores the VALUE first so that, in [any x], [x] pins the type [A] BEFORE
   [the_tag _] triggers [Tagged A] resolution (otherwise the instance is searched
   against an unknown [A] and mis-resolves). *)
Notation anyt t x := (@existT Type (fun A : Type => (A * GoTypeTag A)%type) _ (pair x t)).
Notation any x := (anyt (the_tag _) x).

(** Tag instances for every type put into an [any] (printed / panicked / asserted). *)
#[global] Instance Tagged_bool   : Tagged bool     := TBool.
#[global] Instance Tagged_int    : Tagged int      := TInt64.
#[global] Instance Tagged_float  : Tagged float    := TFloat64.
#[global] Instance Tagged_string : Tagged GoString := TString.
#[global] Instance Tagged_unit   : Tagged unit     := TUnit.
#[global] Instance Tagged_GoU8   : Tagged GoU8     := TU8.
#[global] Instance Tagged_GoI8   : Tagged GoI8     := TI8.
#[global] Instance Tagged_GoU16  : Tagged GoU16    := TU16.
#[global] Instance Tagged_GoI16  : Tagged GoI16    := TI16.
#[global] Instance Tagged_GoU32  : Tagged GoU32    := TU32.
#[global] Instance Tagged_GoI32  : Tagged GoI32    := TI32.
#[global] Instance Tagged_GoI64  : Tagged GoI64    := TI64.

(** ---- Decidable key equality (Go map keys must be COMPARABLE) ----

    Go map keys are restricted to comparable types (the spec: "the comparison
    operators == and != must be fully defined for operands of the key type").
    [key_eqb tag] is that comparison, recovered from the key's [GoTypeTag]: the
    scalar carriers ([int]) use [PrimInt63.eqb], [bool]/[string]/[float] their own
    [eqb], a channel/map handle compares its location.  Slices and [GoAny] are NOT
    comparable key types — Go rejects them — so they get a sentinel ([false]); a
    well-typed program never keys a map on them.  [Comparable tag] is the proof
    that [key_eqb tag] decides Leibniz equality (it holds for the scalar key
    types; NOT for floats, since [NaN <> NaN]). *)
Definition key_eqb {K} (t : GoTypeTag K) : K -> K -> bool :=
  match t in GoTypeTag K' return K' -> K' -> bool with
  | TBool    => Bool.eqb
  | TInt64   => PrimInt63.eqb | TInt    => PrimInt63.eqb | TInt8  => PrimInt63.eqb
  | TInt16   => PrimInt63.eqb | TInt32  => PrimInt63.eqb
  | TUint    => PrimInt63.eqb | TUint8  => PrimInt63.eqb | TUint16 => PrimInt63.eqb
  | TUint32  => PrimInt63.eqb | TUint64 => PrimInt63.eqb
  | TString  => String.eqb
  | TFloat64 => PrimFloat.eqb | TFloat32 => PrimFloat.eqb
  | TU8  => fun a b => PrimInt63.eqb (u8raw a) (u8raw b)
  | TI8  => fun a b => PrimInt63.eqb (i8raw a) (i8raw b)
  | TU16 => fun a b => PrimInt63.eqb (u16raw a) (u16raw b)
  | TI16 => fun a b => PrimInt63.eqb (i16raw a) (i16raw b)
  | TU32 => fun a b => PrimInt63.eqb (u32raw a) (u32raw b)
  | TI32 => fun a b => PrimInt63.eqb (i32raw a) (i32raw b)
  | TI64 => fun a b => Z.eqb (i64raw a) (i64raw b)
  | TUnit => fun _ _ => true
  | TChan _  => fun a b => PrimInt63.eqb (ch_loc a) (ch_loc b)
  | TSlice _ => fun _ _ => false
  | TMap _ _ => fun a b => PrimInt63.eqb (gm_loc a) (gm_loc b)
  end.

(** [Comparable t]: [key_eqb t] decides equality on [K] — the typing side
    condition Go imposes on map keys, made explicit. *)
Definition Comparable {K} (t : GoTypeTag K) : Prop :=
  forall a b : K, key_eqb t a b = true <-> a = b.

(** The scalar key types ARE comparable (used by every map demo: int keys). *)
Lemma comparable_TInt64 : Comparable TInt64.
Proof. intros a b. cbn. apply Uint63.eqb_spec. Qed.

(** ---- World: a CONCRETE proof-only state record (no longer an axiom). ----

    [World] is FULLY CONCRETE — no abstract residue.  [w_refs]/[w_chans]/[w_maps]
    are the mutable-cell / channel / map heaps (each a location [int] -> an
    optional typed cell that stores the value WITH its [GoTypeTag], so an accessor
    can coerce it back to its own view's type), and [w_next] is the next fresh
    location.  Every state primitive (ref/channel/map) is now a DEFINITION over
    these fields, and their laws are THEOREMS — there is no [RawWorld] axiom left.
    Extraction erases the whole record (the world token never appears in emitted
    Go). *)
Definition RefCell : Type := { T : Type & (GoTypeTag T * T)%type }.
Definition RefHeap : Type := int -> option RefCell.
(** A channel cell: the element type [E] with its [GoTypeTag], the FIFO buffer
    (a [list E]), and the closed flag.  The stored [GoTypeTag] lets an accessor
    coerce the buffer back to its own view's element type (they are equal by
    construction; [tag_eq] recovers the proof). *)
Definition ChanCell : Type := { E : Type & (GoTypeTag E * (list E * bool))%type }.
Definition ChanHeap : Type := int -> option ChanCell.
(** A map cell: the key type [K] + its tag, then existentially the value type [V]
    + its tag, then the contents as a finite-support function [K -> option V].
    Like the channel cell, the stored tags let an accessor coerce back to its own
    [K]/[V] view (equal by construction). *)
Definition MapCell : Type :=
  { K : Type & (GoTypeTag K * { V : Type & (GoTypeTag V * (K -> option V))%type })%type }.
Definition MapHeap : Type := int -> option MapCell.
Record World : Type := mkWorld
  { w_refs : RefHeap ; w_chans : ChanHeap ; w_maps : MapHeap ; w_next : int }.


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

(** The [run_*] laws are now THEOREMS (by computation), not axioms. *)
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
(** IO extensionality: equal on every world => equal.  With [IO A := World -> Outcome A]
    this is functional extensionality — a Coq-STDLIB axiom (EXTERNAL, not one of ours).
    Restating the builtins-internal laws over observational equality would drop even
    this; deferred (see ZERO_AXIOMS_PLAN.md, holdout #1). *)
Lemma run_io_inj : forall {A} (m m' : IO A),
  (forall w, run_io m w = run_io m' w) -> m = m'.
Proof. intros A m m' H. apply functional_extensionality. exact H. Qed.

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


(** ---- Fixed-width unsigned integers (precise, computable models) ----

    A [uintN] value is carried by an [int] (PrimInt63) kept reduced mod 2^N by
    masking ([land .. (2^N-1)]) after EVERY operation.  That is EXACTLY Go's
    uintN arithmetic, which wraps mod 2^N.  Because the value always stays in
    [0, 2^N) (well below 2^62), the carrier never approaches the int63 boundary,
    signed and unsigned comparison agree, and the model is faithful to Go.

    These are DEFINITIONS, not axioms — so the model is computable ([vm_compute]
    discharges concrete wrap facts) and adds nothing to the trust base
    (consistency by construction).

    AIRTIGHT TYPE DISTINCTNESS (Go spec "Numeric types": numeric types are defined
    and DISTINCT; "explicit conversions are required when different numeric types
    are mixed").  [GoU8] is its OWN type — a single-field record over the [int]
    carrier — so Rocq's type checker REJECTS mixing a [uint8] with an [int]; the
    only way in is [u8_lit] (the untyped-constant conversion).  The wrap proofs
    stay computable (via [u8raw]), and the plugin ERASES the wrapper in extraction
    ([GoU8] → its int64 carrier, [MkU8]/[u8raw] → identity), so each op still
    lowers to int64 + the explicit mask ([u8_add a b] → [(a + b) & 0xff]) —
    compilable BY CONSTRUCTION, no Go-level wrapper.  [u8_no_implicit] (a [Fail])
    is the build-checked proof that mixing is unrepresentable. *)
(* Go spec "Constants": a constant is typed at use with a REPRESENTABILITY check —
   "it is an error if the constant value cannot be represented as a value of the
   respective type".  So an out-of-range constant is a COMPILE ERROR, NOT a silent
   wrap.  [u8_lit] demands a proof the constant fits ([x < 256], discharged by
   [eq_refl] for a literal in range); there is no masking, so [u8_lit 300] is
   unrepresentable — exactly Go's "constant overflows uint8". *)
Definition u8_lit (x : int) (_ : (x <? 256)%uint63 = true) : GoU8 := MkU8 x.
Definition u8_add (a b : GoU8) : GoU8 := MkU8 (PrimInt63.land (PrimInt63.add (u8raw a) (u8raw b)) 255).
Definition u8_sub (a b : GoU8) : GoU8 := MkU8 (PrimInt63.land (PrimInt63.sub (u8raw a) (u8raw b)) 255).
Definition u8_mul (a b : GoU8) : GoU8 := MkU8 (PrimInt63.land (PrimInt63.mul (u8raw a) (u8raw b)) 255).
Definition u8_eqb (a b : GoU8) : bool := PrimInt63.eqb (u8raw a) (u8raw b).  (* in-range ⇒ exact *)
Definition u8_ltb (a b : GoU8) : bool := PrimInt63.ltb (u8raw a) (u8raw b).  (* in-range ⇒ unsigned = signed *)
Definition u8_leb (a b : GoU8) : bool := PrimInt63.leb (u8raw a) (u8raw b).

(* Build-checked: [uint8] and [int] do NOT mix — no implicit conversion. *)
Fail Definition u8_no_implicit (x : GoU8) : GoU8 := u8_add x (5 : int).
(* Build-checked: an out-of-range constant is UNREPRESENTABLE (Go: "overflows uint8"). *)
Fail Definition u8_const_oob : GoU8 := u8_lit 300 eq_refl.

(* Go's [byte] is a predeclared alias for [uint8] — the faithful [GoU8] record.
   So [s[i]] (a string byte) and a [uint8] are the SAME type, as in Go. *)
Notation GoByte := GoU8.

(** ---- Signed fixed-width integers ----

    [int8] in [-128, 128).  Go's int8 arithmetic wraps two's-complement.  Model:
    mask to 8 bits, then SIGN-EXTEND with [(m ^ 0x80) - 0x80] (flip the sign bit,
    subtract it), taking [m ∈ [0,256)] to [[-128,128)] — exactly what Go's
    [int8(x)] conversion does.  Comparison is SIGNED (values can be negative), so
    it uses [Sint63.ltb] → Go's signed int64 [<].  Computable and faithful; the
    plugin emits the explicit int64 mask + sign-extend, e.g.
    [i8_add a b] → [((((a + b) & 0xff) ^ 0x80) - 0x80)].
    Each is a DISTINCT record over the [int] carrier (like [GoU8]) — the wrapper
    is erased in extraction, so the Go is unchanged.  The [*_norm] helpers stay
    [int -> int] (raw mask + sign-extend); the typed ops wrap with the record
    constructor. *)
Definition i8_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 255) 128) 128.
Definition i8_lit (x : int) (_ : (Sint63.leb (-128)%sint63 x && Sint63.ltb x 128)%bool = true) : GoI8 := MkI8 x.
Definition i8_add (a b : GoI8) : GoI8 := MkI8 (i8_norm (PrimInt63.add (i8raw a) (i8raw b))).
Definition i8_sub (a b : GoI8) : GoI8 := MkI8 (i8_norm (PrimInt63.sub (i8raw a) (i8raw b))).
Definition i8_mul (a b : GoI8) : GoI8 := MkI8 (i8_norm (PrimInt63.mul (i8raw a) (i8raw b))).
Definition i8_eqb (a b : GoI8) : bool := PrimInt63.eqb (i8raw a) (i8raw b).
Definition i8_ltb (a b : GoI8) : bool := Sint63.ltb (i8raw a) (i8raw b).   (* SIGNED comparison *)
Definition i8_leb (a b : GoI8) : bool := Sint63.leb (i8raw a) (i8raw b).

(** [uint16] / [int16] — the same template at width 16 (mask [0xffff]; sign bit
    [0x8000]).  Still fully faithful on the 63-bit carrier: a 16-bit product is
    [< 2^32], far below the [2^62] boundary, so [mul] is exact too. *)
Definition u16_lit (x : int) (_ : (x <? 65536)%uint63 = true) : GoU16 := MkU16 x.
Definition u16_add (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.add (u16raw a) (u16raw b)) 65535).
Definition u16_sub (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.sub (u16raw a) (u16raw b)) 65535).
Definition u16_mul (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.mul (u16raw a) (u16raw b)) 65535).
Definition u16_eqb (a b : GoU16) : bool := PrimInt63.eqb (u16raw a) (u16raw b).
Definition u16_ltb (a b : GoU16) : bool := PrimInt63.ltb (u16raw a) (u16raw b).
Definition u16_leb (a b : GoU16) : bool := PrimInt63.leb (u16raw a) (u16raw b).

Definition i16_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 65535) 32768) 32768.
Definition i16_lit (x : int) (_ : (Sint63.leb (-32768)%sint63 x && Sint63.ltb x 32768)%bool = true) : GoI16 := MkI16 x.
Definition i16_add (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.add (i16raw a) (i16raw b))).
Definition i16_sub (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.sub (i16raw a) (i16raw b))).
Definition i16_mul (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.mul (i16raw a) (i16raw b))).
Definition i16_eqb (a b : GoI16) : bool := PrimInt63.eqb (i16raw a) (i16raw b).
Definition i16_ltb (a b : GoI16) : bool := Sint63.ltb (i16raw a) (i16raw b).
Definition i16_leb (a b : GoI16) : bool := Sint63.leb (i16raw a) (i16raw b).

(* Build-checked (Go spec "Numeric types": distinct types, no implicit mixing):
   neither a typed value of another numeric type nor an [int] may be passed. *)
Fail Definition i8_no_implicit  (x : GoI8)  : GoI8  := i8_add  x (5 : int).
Fail Definition u16_no_implicit (x : GoU16) : GoU16 := u16_add x (5 : int).
Fail Definition i16_no_implicit (x : GoI16) : GoI16 := i16_add x (5 : int).
(* Cross-WIDTH too: [uint8] and [uint16] are distinct types — no implicit widen. *)
Fail Definition u8_u16_no_mix (x : GoU8) (y : GoU16) : GoU16 := u16_add y x.

(* Build-checked (Go spec "Constants"): out-of-range constants are UNREPRESENTABLE
   (a compile error), per width — no silent wrap. *)
Fail Definition i8_const_oob  : GoI8  := i8_lit  200    eq_refl.   (* > 127 *)
Fail Definition u16_const_oob : GoU16 := u16_lit 70000  eq_refl.   (* >= 2^16 *)
Fail Definition i16_const_oob : GoI16 := i16_lit 40000  eq_refl.   (* > 32767 *)

(** ---- Fixed-width bitwise operators (Go spec "Arithmetic operators": [& | ^ &^],
    and unary [^] complement) ----

    Bitwise AND / OR / XOR / AND-NOT and unary complement on the fixed-width
    types.  TOTAL and panic-free (unlike shifts, whose count can panic).
    Faithful by construction:
    - [uintN]: AND/OR/XOR of two in-range values stay in [0,2^N), so no mask is
      needed; AND-NOT and complement flip within the width via [lxor _ (2^N-1)].
    - [intN]: the sign-extended carrier already makes the raw bitwise op correct,
      but we re-[norm] (idempotent) so every result is manifestly a valid [intN].
    Go's [&^] (AND-NOT) and unary [^] (complement) are single operators.  The
    plugin emits the bare Go infix [& | ^ &^] / unary [^] (no wrap) — faithful
    because the operands are in range / sign-extended (verified on int64). *)
Definition u8_and     (a b : GoU8)  : GoU8  := MkU8  (PrimInt63.land (u8raw a) (u8raw b)).
Definition u8_or      (a b : GoU8)  : GoU8  := MkU8  (PrimInt63.lor  (u8raw a) (u8raw b)).
Definition u8_xor     (a b : GoU8)  : GoU8  := MkU8  (PrimInt63.lxor (u8raw a) (u8raw b)).
Definition u8_andnot  (a b : GoU8)  : GoU8  := MkU8  (PrimInt63.land (u8raw a) (PrimInt63.lxor (u8raw b) 255)).
Definition u8_not     (a   : GoU8)  : GoU8  := MkU8  (PrimInt63.lxor (u8raw a) 255).
Definition i8_and     (a b : GoI8)  : GoI8  := MkI8  (i8_norm (PrimInt63.land (i8raw a) (i8raw b))).
Definition i8_or      (a b : GoI8)  : GoI8  := MkI8  (i8_norm (PrimInt63.lor  (i8raw a) (i8raw b))).
Definition i8_xor     (a b : GoI8)  : GoI8  := MkI8  (i8_norm (PrimInt63.lxor (i8raw a) (i8raw b))).
Definition i8_andnot  (a b : GoI8)  : GoI8  := MkI8  (i8_norm (PrimInt63.land (i8raw a) (PrimInt63.lxor (i8raw b) 255))).
Definition i8_not     (a   : GoI8)  : GoI8  := MkI8  (i8_norm (PrimInt63.lxor (i8raw a) 255)).
Definition u16_and    (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (u16raw a) (u16raw b)).
Definition u16_or     (a b : GoU16) : GoU16 := MkU16 (PrimInt63.lor  (u16raw a) (u16raw b)).
Definition u16_xor    (a b : GoU16) : GoU16 := MkU16 (PrimInt63.lxor (u16raw a) (u16raw b)).
Definition u16_andnot (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (u16raw a) (PrimInt63.lxor (u16raw b) 65535)).
Definition u16_not    (a   : GoU16) : GoU16 := MkU16 (PrimInt63.lxor (u16raw a) 65535).
Definition i16_and    (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.land (i16raw a) (i16raw b))).
Definition i16_or     (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.lor  (i16raw a) (i16raw b))).
Definition i16_xor    (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.lxor (i16raw a) (i16raw b))).
Definition i16_andnot (a b : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.land (i16raw a) (PrimInt63.lxor (i16raw b) 65535))).
Definition i16_not    (a   : GoI16) : GoI16 := MkI16 (i16_norm (PrimInt63.lxor (i16raw a) 65535)).

(* Build-checked: bitwise ops respect type distinctness too (no implicit mix). *)
Fail Definition u8_and_no_implicit (x : GoU8) : GoU8 := u8_and x (5 : int).

(** ---- Fixed-width shifts (Go spec "Arithmetic operators": [<< >>]) ----

    Left / right shift on the fixed-width types.  Unlike the bitwise ops, a shift
    can PANIC: Go panics if the count is negative.  So — exactly like [div_nz] —
    the shift is EVIDENCE-CARRYING: it demands a proof the count is non-negative
    ([0 <= k], discharged by [eq_refl] for a literal), making the panic
    unreachable (safe-by-construction).  There is NO upper limit on the count
    (Go: an over-width shift gives 0 / sign-fill, not UB); the primitives agree —
    [lsl]/[lsr] give 0 for [k >= width], [asr] fills with the sign bit.
    - [<<]: [uintN] truncates to the width ([(x<<k) mod 2^N], via [land]); [intN]
      is two's-complement (sign-extend via [norm]).
    - [>>]: [uintN] is LOGICAL ([lsr]); [intN] is ARITHMETIC ([asr]) — sign-
      preserving, truncating toward −∞, NOT toward zero like [/] ([-3>>1 = -2],
      whereas [-3/2 = -1]).
    The plugin emits Go [x << k] / [x >> k]: for [>>], the int64 carrier is
    non-negative for [uintN] (so Go's [>>] is logical) and sign-extended for
    [intN] (so Go's [>>] is arithmetic) — both correct with no mask. *)
Definition u8_shl  (x : GoU8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoU8  := MkU8  (PrimInt63.land (PrimInt63.lsl (u8raw x) k) 255).
Definition u8_shr  (x : GoU8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoU8  := MkU8  (PrimInt63.lsr (u8raw x) k).
Definition i8_shl  (x : GoI8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoI8  := MkI8  (i8_norm (PrimInt63.lsl (i8raw x) k)).
Definition i8_shr  (x : GoI8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoI8  := MkI8  (i8_norm (PrimInt63.asr (i8raw x) k)).
Definition u16_shl (x : GoU16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.lsl (u16raw x) k) 65535).
Definition u16_shr (x : GoU16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU16 := MkU16 (PrimInt63.lsr (u16raw x) k).
Definition i16_shl (x : GoI16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI16 := MkI16 (i16_norm (PrimInt63.lsl (i16raw x) k)).
Definition i16_shr (x : GoI16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI16 := MkI16 (i16_norm (PrimInt63.asr (i16raw x) k)).

(* Build-checked: a NEGATIVE shift count is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_shl_neg : GoU8 := u8_shl (u8_lit 1 eq_refl) (-1)%sint63 eq_refl.

(** ---- Numeric conversions (Go spec "Conversions") ----

    "When converting between integer types, if the value is a signed integer, it
    is sign extended to implicit infinite precision ... It is then truncated to
    fit in the result type's size."  These are the EXPLICIT conversions the
    "Numeric types" rule requires to mix distinct types — the type checker rejects
    implicit mixing (the [*_no_implicit] [Fail]s), so a value crosses types only
    through one of these.

    Every conversion routes through the [int] carrier, which already holds each
    fixed-width value's exact mathematical value (sign-extended for [intN],
    zero-extended for [uintN]):
    - [int_of_FW] WIDENS to [int] — value preserved (every [uintN]/[intN] fits in
      [int]); lowers to identity (the carrier is already int64).
    - [FW_of_int] NARROWS [int] to the width — TRUNCATE ([land] to [uintN], or
      mask+sign-extend [norm] to [intN]) — exactly Go's [uint8(x)]/[int8(x)].  No
      representability proof (unlike [*_lit]): a conversion truncates, it does not
      reject.  Composition handles cross-width ([uint8(int16val)] =
      [u8_of_int (int_of_i16 x)] = low 8 bits, faithful). *)
Definition int_of_u8  (x : GoU8)  : int := u8raw x.
Definition int_of_i8  (x : GoI8)  : int := i8raw x.
Definition int_of_u16 (x : GoU16) : int := u16raw x.
Definition int_of_i16 (x : GoI16) : int := i16raw x.
Definition u8_of_int  (x : int) : GoU8  := MkU8  (PrimInt63.land x 255).
Definition i8_of_int  (x : int) : GoI8  := MkI8  (i8_norm x).
Definition u16_of_int (x : int) : GoU16 := MkU16 (PrimInt63.land x 65535).
Definition i16_of_int (x : int) : GoI16 := MkI16 (i16_norm x).

(* Build-checked: a conversion takes an [int], NOT another fixed-width type — so a
   cross-type conversion MUST go through [int] (e.g. [u8_of_int (int_of_i16 y)]),
   never [u8_of_int y] directly. *)
Fail Definition u8_of_i16_direct (y : GoI16) : GoU8 := u8_of_int y.

(** ---- Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]) ----
    EVIDENCE-CARRYING like [div_nz]: demand the divisor be non-zero (Go panics on a
    zero divisor), so the panic is unreachable (safe-by-construction).
    - [uintN]: the carrier is non-negative, so the SIGNED primitives [divs]/[mods]
      compute the UNSIGNED quotient/remainder; the result is in range (quotient
      <= dividend, |remainder| < divisor), no mask.
    - [intN]: SIGNED div/mod (truncate toward zero), wrapped to the width ([norm]) —
      this is where the most-negative / [-1] overflow lands: Go [int8(-128)/int8(-1)
      = -128] (two's-complement wrap), and [norm] gives exactly that. *)
Definition u8_div  (a b : GoU8)  (_ : (PrimInt63.eqb (u8raw b)  0) = false) : GoU8  := MkU8  (PrimInt63.divs (u8raw a) (u8raw b)).
Definition u8_mod  (a b : GoU8)  (_ : (PrimInt63.eqb (u8raw b)  0) = false) : GoU8  := MkU8  (PrimInt63.mods (u8raw a) (u8raw b)).
Definition i8_div  (a b : GoI8)  (_ : (PrimInt63.eqb (i8raw b)  0) = false) : GoI8  := MkI8  (i8_norm (PrimInt63.divs (i8raw a) (i8raw b))).
Definition i8_mod  (a b : GoI8)  (_ : (PrimInt63.eqb (i8raw b)  0) = false) : GoI8  := MkI8  (i8_norm (PrimInt63.mods (i8raw a) (i8raw b))).
Definition u16_div (a b : GoU16) (_ : (PrimInt63.eqb (u16raw b) 0) = false) : GoU16 := MkU16 (PrimInt63.divs (u16raw a) (u16raw b)).
Definition u16_mod (a b : GoU16) (_ : (PrimInt63.eqb (u16raw b) 0) = false) : GoU16 := MkU16 (PrimInt63.mods (u16raw a) (u16raw b)).
Definition i16_div (a b : GoI16) (_ : (PrimInt63.eqb (i16raw b) 0) = false) : GoI16 := MkI16 (i16_norm (PrimInt63.divs (i16raw a) (i16raw b))).
Definition i16_mod (a b : GoI16) (_ : (PrimInt63.eqb (i16raw b) 0) = false) : GoI16 := MkI16 (i16_norm (PrimInt63.mods (i16raw a) (i16raw b))).

(* Build-checked: a ZERO divisor is UNREPRESENTABLE (Go panics on it). *)
Fail Definition u8_div_zero : GoU8 := u8_div (u8_lit 1 eq_refl) (u8_lit 0 eq_refl) eq_refl.

(** ---- uint32 / int32 — the SAME template at width 32 ----

    Distinct records over the [int] carrier, same as the narrower widths.  Mask
    [0xffffffff], sign bit [0x80000000].  Every op (add/sub, comparison, bitwise,
    shift, div/mod, conversions) is faithful on the 63-bit carrier: a 32-bit
    add/sub/shift/div result is [< 2^33], far below [2^62].

    [u32_mul]/[i32_mul] ARE defined (mask-after-multiply).  A 32-bit product can
    reach [(2^32-1)^2 ≈ 2^64], exceeding the 63-bit carrier — but the masked LOW 32
    bits are still EXACT, so no Z model is needed here.  [PrimInt63.mul] reduces mod
    [2^63] and [2^32 | 2^63], hence [(a*b mod 2^63) mod 2^32 = a*b mod 2^32]: losing
    the carrier's high bits never disturbs the low [w < 63] bits the mask keeps.
    (Only a 63-/64-bit-WIDE product genuinely needs the Z-based wide-int model.)
    Machine-checked: [spec_u32_mul_wrap]/[spec_i32_mul_wrap] in main.v. *)
Definition u32_lit (x : int) (_ : (x <? 4294967296)%uint63 = true) : GoU32 := MkU32 x.
Definition u32_add (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.add (u32raw a) (u32raw b)) 4294967295).
Definition u32_sub (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.sub (u32raw a) (u32raw b)) 4294967295).
Definition u32_mul (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.mul (u32raw a) (u32raw b)) 4294967295).  (* low 32 bits exact: 2^32 | 2^63 *)
Definition u32_eqb (a b : GoU32) : bool := PrimInt63.eqb (u32raw a) (u32raw b).
Definition u32_ltb (a b : GoU32) : bool := PrimInt63.ltb (u32raw a) (u32raw b).
Definition u32_leb (a b : GoU32) : bool := PrimInt63.leb (u32raw a) (u32raw b).
Definition u32_and    (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (u32raw a) (u32raw b)).
Definition u32_or     (a b : GoU32) : GoU32 := MkU32 (PrimInt63.lor  (u32raw a) (u32raw b)).
Definition u32_xor    (a b : GoU32) : GoU32 := MkU32 (PrimInt63.lxor (u32raw a) (u32raw b)).
Definition u32_andnot (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (u32raw a) (PrimInt63.lxor (u32raw b) 4294967295)).
Definition u32_not    (a   : GoU32) : GoU32 := MkU32 (PrimInt63.lxor (u32raw a) 4294967295).
Definition u32_shl (x : GoU32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.lsl (u32raw x) k) 4294967295).
Definition u32_shr (x : GoU32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU32 := MkU32 (PrimInt63.lsr (u32raw x) k).
Definition u32_div (a b : GoU32) (_ : (PrimInt63.eqb (u32raw b) 0) = false) : GoU32 := MkU32 (PrimInt63.divs (u32raw a) (u32raw b)).
Definition u32_mod (a b : GoU32) (_ : (PrimInt63.eqb (u32raw b) 0) = false) : GoU32 := MkU32 (PrimInt63.mods (u32raw a) (u32raw b)).
Definition int_of_u32 (x : GoU32) : int := u32raw x.
Definition u32_of_int (x : int) : GoU32 := MkU32 (PrimInt63.land x 4294967295).

Definition i32_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 4294967295) 2147483648) 2147483648.
Definition i32_lit (x : int) (_ : (Sint63.leb (-2147483648)%sint63 x && Sint63.ltb x 2147483648)%bool = true) : GoI32 := MkI32 x.
Definition i32_add (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.add (i32raw a) (i32raw b))).
Definition i32_sub (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.sub (i32raw a) (i32raw b))).
Definition i32_mul (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.mul (i32raw a) (i32raw b))).  (* low 32 bits exact, then sign-extend *)
Definition i32_eqb (a b : GoI32) : bool := PrimInt63.eqb (i32raw a) (i32raw b).
Definition i32_ltb (a b : GoI32) : bool := Sint63.ltb (i32raw a) (i32raw b).
Definition i32_leb (a b : GoI32) : bool := Sint63.leb (i32raw a) (i32raw b).
Definition i32_and    (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.land (i32raw a) (i32raw b))).
Definition i32_or     (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.lor  (i32raw a) (i32raw b))).
Definition i32_xor    (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.lxor (i32raw a) (i32raw b))).
Definition i32_andnot (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.land (i32raw a) (PrimInt63.lxor (i32raw b) 4294967295))).
Definition i32_not    (a   : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.lxor (i32raw a) 4294967295)).
Definition i32_shl (x : GoI32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI32 := MkI32 (i32_norm (PrimInt63.lsl (i32raw x) k)).
Definition i32_shr (x : GoI32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI32 := MkI32 (i32_norm (PrimInt63.asr (i32raw x) k)).
Definition i32_div (a b : GoI32) (_ : (PrimInt63.eqb (i32raw b) 0) = false) : GoI32 := MkI32 (i32_norm (PrimInt63.divs (i32raw a) (i32raw b))).
Definition i32_mod (a b : GoI32) (_ : (PrimInt63.eqb (i32raw b) 0) = false) : GoI32 := MkI32 (i32_norm (PrimInt63.mods (i32raw a) (i32raw b))).
Definition int_of_i32 (x : GoI32) : int := i32raw x.
Definition i32_of_int (x : int) : GoI32 := MkI32 (i32_norm x).

(* Build-checked: u32/i32 are distinct, out-of-range constants unrepresentable. *)
Fail Definition u32_no_implicit (x : GoU32) : GoU32 := u32_add x (5 : int).
Fail Definition u32_const_oob   : GoU32 := u32_lit 5000000000 eq_refl.   (* >= 2^32 *)

(** ---- int64 — FULL-WIDTH signed 64-bit (Go spec "Numeric types") ----

    The faithful model of Go's [int64] / (64-bit) [int].  Unlike the narrow
    [GoU8]…[GoI32] records (masked [int] carriers, exact because the width fits the
    63-bit primitive), int64 needs the WHOLE 64-bit range — one bit MORE than the
    63-bit [int] — so it is carried by [Z] and normalised mod [2^64] into the signed
    range after every op.  [wrap64] is the two's-complement wrap; it is the IDENTITY
    on in-range values (so a no-overflow op equals the exact mathematical result —
    [i64_add_no_overflow_exact] in main.v), and at the boundary [2^63-1 + 1] wraps to
    [-2^63] exactly like Go ([spec_i64_add_wrap]).  Extraction erases the wrapper and
    emits BARE Go int64 ops ([a + b], …): Go's int64 wraps natively at [2^64], so the
    mask the narrow widths need is here unnecessary.  Comparison is signed [Z]
    comparison — valid because every stored value is normalised into [-2^63, 2^63). *)
Definition wrap64 (z : Z) : Z :=
  (Z.modulo (z + 9223372036854775808) 18446744073709551616 - 9223372036854775808)%Z.
Definition in_i64 (z : Z) : bool :=
  andb (-9223372036854775808 <=? z)%Z (z <? 9223372036854775808)%Z.
(* Smart literal: DEMANDS the constant fit int64 (Go's compile-time representability
   check); an out-of-range literal is unrepresentable ([i64_const_oob] Fail). *)
Definition i64_lit (z : Z) (_ : in_i64 z = true) : GoI64 := MkI64 z.
Definition i64_add (a b : GoI64) : GoI64 := MkI64 (wrap64 (i64raw a + i64raw b)).
Definition i64_sub (a b : GoI64) : GoI64 := MkI64 (wrap64 (i64raw a - i64raw b)).
Definition i64_mul (a b : GoI64) : GoI64 := MkI64 (wrap64 (i64raw a * i64raw b)).
Definition i64_eqb (a b : GoI64) : bool := Z.eqb (i64raw a) (i64raw b).
Definition i64_ltb (a b : GoI64) : bool := Z.ltb (i64raw a) (i64raw b).
Definition i64_leb (a b : GoI64) : bool := Z.leb (i64raw a) (i64raw b).

(* Build-checked: a constant that does not fit int64 is UNREPRESENTABLE (Go's
   constant-overflow compile error), and int64 does not implicitly mix with [int]. *)
Fail Definition i64_const_oob : GoI64 := i64_lit 9223372036854775808%Z eq_refl.  (* = 2^63 *)
Fail Definition i64_no_implicit (x : GoI64) : GoI64 := i64_add x (5 : int).

(** ---- Builtins ---- *)

(** [print]/[println] write to stdout — a real effect, but the proof-only world
    models no output log, so semantically they are world-passthroughs (no law reasons
    about output; the real output happens in the extracted Go).  Lowered by NAME. *)
Definition print   (_ : list GoAny) : IO unit := fun w => ORet tt w.
Definition println (_ : list GoAny) : IO unit := fun w => ORet tt w.

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

(** [defer_call f] (Go spec "Defer statements"): Go's [defer] keyword — schedule
    [f] to run when the enclosing *function* returns (LIFO across all defers, on both normal and
    panic exit), and continue immediately.  This is FUNCTION-scoped, unlike the
    block-scoped [with_defer]: deferred calls in a loop accumulate and all run
    at function return.  Lowers to [defer func(){ f }()] (Go provides the
    function-scoping, LIFO ordering, and run-at-return). *)
(** Proof-only: the deferred effect (run at function return) is idealised away in the
    sequential world — no law reasons about it; the real [defer] is in the emitted Go. *)
Definition defer_call (_ : IO unit) : IO unit := fun w => ORet tt w.


(** [type_assert tag v] (Go spec "Type assertions") asserts that [v : GoAny] holds
    a value of Go type [T].  Panics (like Go's [v.(T)]) if the runtime type does not
    match.

    ESCAPE HATCH: the raw panicking form, safe only inside [catch] or when the
    runtime type is already known.  Prefer [type_assert_safe] (below), the
    safe-by-construction default.

    Now a DEFINITION (not an axiom): the tagged [GoAny] carries the value's runtime
    [GoTypeTag], so [tag_coerce] checks it against the target [tag] and recovers the
    value when they agree; a mismatch PANICS, exactly Go's [v.(T)].  Lowered by NAME
    to [v.(T)] (body suppressed). *)
Definition type_assert {T : Type} (tag : GoTypeTag T) (a : GoAny) : IO T :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => ret t
      | None   => panic (anyt TUnit tt)   (* runtime-type mismatch: Go panics *)
      end
  end.

(** Read-after-assert: asserting [anyt tag x] to its OWN tag returns [x] — a THEOREM
    (was an axiom), from [tag_coerce_refl]. *)
Theorem type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (anyt tag x) = ret x.
Proof. intros T tag x. unfold type_assert. rewrite tag_coerce_refl. reflexivity. Qed.

(** Safe checked assertion (the safe-by-construction default for [GoAny]) — now a
    DEFINITION.  [type_assert_safe tag a (fun v ok => body)] lowers to Go's native
    two-value form [v, ok := a.(T); body]: when the runtime tag matches [T], [ok =
    true] and [v] is the value; otherwise [ok = false] and [v = zero_val tag].
    Because the caller must handle [ok = false], it cannot panic.  CPS like [recv_ok]. *)
Definition type_assert_safe {T B : Type}
  (tag : GoTypeTag T) (a : GoAny) (k : T -> bool -> IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => k t true
      | None   => k (zero_val tag) false
      end
  end.

(** Build-checked: a WRONG-type assertion does NOT silently return the value — the
    coercion is [None], so the result is a panic / [ok = false], never [ret x]. *)
Example type_assert_safe_ok : forall {B} (x : int) (k : int -> bool -> IO B),
  type_assert_safe TInt64 (anyt TInt64 x) k = k x true.
Proof. intros B x k. unfold type_assert_safe. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_assert_safe_mismatch : forall {B} (x : int) (k : bool -> bool -> IO B),
  type_assert_safe TBool (anyt TInt64 x) k = k false false.
Proof. intros B x k. reflexivity. Qed.

(** ---- GoMap ----

    [GoMap K V] models Go's [map[K]V].  Operations are modelled as pure
    functions returning updated maps; extraction emits in-place mutations,
    which are semantically equivalent in single-goroutine programs since
    maps are reference types with no observable aliasing difference.

    [map_make] is in [IO] because it allocates a new map reference.
    [map_get_opt] returns [option V]; its extraction is deferred until we
    handle [option] lowering properly. *)

(** The allocators are now DEFINITIONS (not axioms): a [GoMap]/[GoChan] is a
    concrete location handle, so they simply mint one.  [map_empty] is the nil map
    (a fixed [MkMap 0] handle — [map_set] on it would panic, like Go's nil map);
    the [IO] allocators take a fresh location from [w_next] and bump it.  The map
    CONTENTS live in the concrete [w_maps] heap, where [map_sel]/[map_upd] are
    DEFINITIONS and the map laws are THEOREMS.  Lowered by name ([make(map[K]V)] /
    nil), the bodies are proof-only. *)
Definition map_empty {K V : Type} : GoMap K V := MkMap 0%uint63.

(** [map_make_typed kt vt] creates an empty map with concrete key/value types.
    The [GoTypeTag] witnesses survive extraction so the plugin can emit
    [make(map[K]V)] with the correct Go type — unlike bare [map_make] which
    loses the types to erasure and falls back to [map[any]any].

    NOTE: Go map access never panics on a missing key — it returns the zero
    value (two-value form gives [false] for [ok]).  This differs from slice
    indexing, which DOES panic out of bounds. *)
Definition map_make_typed {K V : Type} (kt : GoTypeTag K) (vt : GoTypeTag V) : IO (GoMap K V) :=
  fun w => let l := w_next w in
           ORet (MkMap l)
                (mkWorld (w_refs w) (w_chans w)
                         (fun k => if PrimInt63.eqb k l
                                   then Some (existT _ K (kt, existT _ V (vt, fun _ => None)))
                                   else w_maps w k)
                         (PrimInt63.add l 1%uint63)).

(** Untyped fallback — loses key/value types to erasure, emits map[any]any.  No
    tags to seed a cell, so it just mints the handle (the first [map_set] creates
    the typed cell; an unwritten read is [None], Go's empty-map behaviour). *)
Definition map_make {K V : Type} : IO (GoMap K V) :=
  fun w => ORet (MkMap (w_next w))
                (mkWorld (w_refs w) (w_chans w) (w_maps w)
                         (PrimInt63.add (w_next w) 1%uint63)).

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
(** The map STATE accessors/updates are now DEFINITIONS over [w_maps] (no longer
    axioms).  Like channels, [GoMap] carries no tag, so the accessors THREAD the
    key + value [GoTypeTag]s; they coerce the cell's stored contents (a function
    [K' -> option V']) to the caller's [K -> option V] view (equal by construction,
    [tag_eq] recovers the proofs).  Each update REWRITES the cell with the caller's
    tags, so a read round-trips via [tag_eq_refl] (just as for channels). *)
Definition map_get_fn {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                       (m : GoMap K V) (w : World) : K -> option V :=
  match w_maps w (gm_loc m) with
  | Some (existT _ _ (kt', existT _ _ (vt', f))) =>
      match tag_eq kt kt', tag_eq vt vt' with
      | Some pk, Some pv =>
          fun k => eq_rect _ (fun Y : Type => option Y)
                           (f (eq_rect _ (fun X : Type => X) k _ pk)) _ (eq_sym pv)
      | _, _ => fun _ => None
      end
  | None => fun _ => None
  end.
Definition map_write {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                      (m : GoMap K V) (f : K -> option V) (w : World) : World :=
  mkWorld (w_refs w) (w_chans w)
          (fun l => if PrimInt63.eqb l (gm_loc m)
                    then Some (existT _ K (kt, existT _ V (vt, f)))
                    else w_maps w l)
          (w_next w).
Definition map_sel {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : option V :=
  map_get_fn kt vt m w k.
Definition map_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (v : V) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then Some v else map_get_fn kt vt m w k') w.
Definition map_rem {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then None else map_get_fn kt vt m w k') w.
(** [map_size] is proof-only (the plugin lowers [map_len] by name to Go [len(m)]);
    its value is never observed, so a placeholder suffices. *)
Definition map_size {K V} (m : GoMap K V) (w : World) : GoInt := 0%uint63.

(** Read-back-after-write: [map_get_fn] of a [map_write] (with the SAME tags) is
    the written function — via [eqb_refl] (location hit) + [tag_eq_refl] (the K/V
    coercions become identities, then eta). *)
Lemma map_get_fn_write_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) m f w,
  map_get_fn kt vt m (map_write kt vt m f w) = f.
Proof.
  intros K V kt vt m f w. unfold map_get_fn, map_write. cbn.
  rewrite (Uint63.eqb_refl (gm_loc m)), !tag_eq_refl. reflexivity.
Qed.

(** The map OPERATIONS, DEFINED over the abstract heap state above; their [run_*]
    laws are now THEOREMS.  Extraction lowers each by NAME to Go map syntax (the
    proof-only [map_sel]/[map_upd]/[map_rem]/[map_size] bodies are suppressed). *)
Definition map_get_opt {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO (option V) :=
  fun w => ORet (map_sel kt vt k m w) w.
Definition map_len {K V} (m : GoMap K V) : IO GoInt :=
  fun w => ORet (map_size m w) w.
(** [map_get_or k default m]: the value at [k], or [default] if absent. *)
Definition map_get_or {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) : IO V :=
  fun w => ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
Definition map_set {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) : IO unit :=
  fun w => ORet tt (map_upd kt vt k v m w).
Definition map_delete {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) : IO unit :=
  fun w => ORet tt (map_rem kt vt k m w).

Lemma run_map_get_opt : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_get_opt kt vt k m) w = ORet (map_sel kt vt k m w) w.
Proof. reflexivity. Qed.
Lemma run_map_len : forall {K V} (m : GoMap K V) (w : World),
  run_io (map_len m) w = ORet (map_size m w) w.
Proof. reflexivity. Qed.
Lemma run_map_get_or : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (default : V) (m : GoMap K V) (w : World),
  run_io (map_get_or kt vt k default m) w =
  ORet (match map_sel kt vt k m w with Some v => v | None => default end) w.
Proof. reflexivity. Qed.
Lemma run_map_set : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  run_io (map_set kt vt k v m) w = ORet tt (map_upd kt vt k v m w).
Proof. reflexivity. Qed.
Lemma run_map_delete : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V) (w : World),
  run_io (map_delete kt vt k m) w = ORet tt (map_rem kt vt k m w).
Proof. reflexivity. Qed.

(** Heap-interface laws — how [map_sel] reads after each update — now THEOREMS.
    The hypotheses make explicit the side conditions Go imposes (and that the old
    unconditional axioms silently assumed): the key must be self-equal under
    [key_eqb] (true for comparable keys, FALSE for a [NaN] float key — which Go's
    map genuinely does not round-trip), and [_diff] needs the key type Comparable
    (so distinct keys compare false).  The demos discharge them via
    [comparable_TInt64]. *)
Theorem map_sel_upd_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v : V) (m : GoMap K V) (w : World),
  key_eqb kt k k = true ->
  map_sel kt vt k m (map_upd kt vt k v m w) = Some v.
Proof.
  intros K V kt vt k v m w Hk. unfold map_sel, map_upd.
  rewrite map_get_fn_write_same. cbn. rewrite Hk. reflexivity.
Qed.
Theorem map_sel_upd_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 ->
  map_sel kt vt k1 m (map_upd kt vt k2 v m w) = map_sel kt vt k1 m w.
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne. unfold map_sel, map_upd.
  rewrite map_get_fn_write_same. cbn.
  destruct (key_eqb kt k2 k1) eqn:E.
  - exfalso. apply Hne. symmetry. apply Hcmp. exact E.
  - reflexivity.
Qed.
Theorem map_sel_rem : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V) (w : World),
  key_eqb kt k k = true ->
  map_sel kt vt k m (map_rem kt vt k m w) = None.
Proof.
  intros K V kt vt k m w Hk. unfold map_sel, map_rem.
  rewrite map_get_fn_write_same. cbn. rewrite Hk. reflexivity.
Qed.
Theorem map_sel_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  w_maps w 0%uint63 = None ->
  map_sel kt vt k (@map_empty K V) w = None.
Proof.
  intros K V kt vt k w Hw. unfold map_sel, map_get_fn, map_empty. cbn.
  rewrite Hw. reflexivity.
Qed.

(** GET-AFTER-WRITE laws — now THEOREMS, derived from the heap interface (these
    were a machine-checked-degenerate axiom under the old pure read). *)
(** A comparable key is self-equal under [key_eqb] (the [_same]/[_rem] side
    condition, discharged from [Comparable]). *)
Lemma comparable_key_refl : forall {K} (t : GoTypeTag K) (k : K),
  Comparable t -> key_eqb t k k = true.
Proof. intros K t k Hc. apply (proj2 (Hc k k)). reflexivity. Qed.

Lemma map_get_set_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v : V) (m : GoMap K V),
  Comparable kt ->
  bind (map_set kt vt k v m) (fun _ => map_get_opt kt vt k m) =
  bind (map_set kt vt k v m) (fun _ => ret (Some v)).
Proof.
  intros K V kt vt k v m Hcmp. apply run_io_inj. intro w.
  rewrite !run_bind, !run_map_set. cbn.
  rewrite run_map_get_opt, map_sel_upd_same by (apply comparable_key_refl; exact Hcmp).
  rewrite run_ret. reflexivity.
Qed.

Lemma map_get_delete_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V),
  Comparable kt ->
  bind (map_delete kt vt k m) (fun _ => map_get_opt kt vt k m) =
  bind (map_delete kt vt k m) (fun _ => ret (@None V)).
Proof.
  intros K V kt vt k m Hcmp. apply run_io_inj. intro w.
  rewrite !run_bind, !run_map_delete. cbn.
  rewrite run_map_get_opt, map_sel_rem by (apply comparable_key_refl; exact Hcmp).
  rewrite run_ret. reflexivity.
Qed.

(** Reading the empty (nil) map gives [None] — in a world where its location is
    unallocated (Go's nil map reads the zero value for every key). *)
Lemma map_get_empty : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (w : World),
  w_maps w 0%uint63 = None ->
  run_io (@map_get_opt K V kt vt k map_empty) w = ORet None w.
Proof.
  intros K V kt vt k w Hw. rewrite run_map_get_opt, map_sel_empty by exact Hw. reflexivity.
Qed.

(** Setting key [k2] leaves the read at a different key [k1] unchanged. *)
Lemma map_get_set_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 ->
  run_io (bind (map_set kt vt k2 v m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_upd kt vt k2 v m w).
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne.
  rewrite run_bind, run_map_set. cbn.
  rewrite run_map_get_opt, map_sel_upd_diff by assumption. reflexivity.
Qed.

(** [map_get_or] hits the stored value when present, falls back when absent. *)
Lemma map_get_or_hit : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (v default : V) (m : GoMap K V) (w : World),
  map_sel kt vt k m w = Some v -> run_io (map_get_or kt vt k default m) w = ORet v w.
Proof. intros K V kt vt k v default m w H. rewrite run_map_get_or, H. reflexivity. Qed.
Lemma map_get_or_miss : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (default : V) (m : GoMap K V) (w : World),
  map_sel kt vt k m w = None -> run_io (map_get_or kt vt k default m) w = ORet default w.
Proof. intros K V kt vt k default m w H. rewrite run_map_get_or, H. reflexivity. Qed.

(** [clear(m)] (Go 1.21): remove ALL entries — write the everywhere-[None]
    function.  [map_sel_clear] (every key reads [None]) is now a THEOREM, so
    GET-AFTER-CLEAR is too. *)
Definition map_clear_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                         (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun _ => None) w.
Definition map_clear {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) : IO unit :=
  fun w => ORet tt (map_clear_upd kt vt m w).
Lemma run_map_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (m : GoMap K V) (w : World),
  run_io (map_clear kt vt m) w = ORet tt (map_clear_upd kt vt m w).
Proof. reflexivity. Qed.
Theorem map_sel_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k : K) (m : GoMap K V) (w : World),
  map_sel kt vt k m (map_clear_upd kt vt m w) = None.
Proof. intros. unfold map_sel, map_clear_upd. rewrite map_get_fn_write_same. reflexivity. Qed.

Lemma map_get_clear : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (m : GoMap K V),
  bind (map_clear kt vt m) (fun _ => map_get_opt kt vt k m) =
  bind (map_clear kt vt m) (fun _ => ret (@None V)).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, !run_map_clear. cbn.
  rewrite run_map_get_opt, map_sel_clear, run_ret. reflexivity.
Qed.

(** ---- GoChan ----

    [GoChan A] models Go's [chan T].  [make_chan] allocates an unbuffered
    channel — send blocks until a receiver is ready, so an unbuffered channel
    requires a complementary goroutine (step 5).  [make_chan_buf n] allocates
    a buffered channel with capacity [n]; send does not block until the buffer
    is full, making single-goroutine use safe when n > 0.

    Ownership: whoever holds the [GoChan A] value owns the channel endpoint.
    Session-type proofs (step 6) will enforce protocol compliance at the Rocq
    type level, with zero runtime cost. *)

(** The channel allocators are now DEFINITIONS (not axioms): a [GoChan] is a
    concrete location handle, minted from a fresh [w_next] location, and the new
    channel's cell is INITIALISED in [w_chans] (empty buffer, not closed, tagged
    with the element type [tag]).  Lowered by name to [make(chan T)] /
    [make(chan T, n)]; the world-threading body is proof-only. *)
Definition make_chan {A : Type} (tag : GoTypeTag A) : IO (GoChan A) :=
  fun w => let l := w_next w in
           ORet (MkChan l)
                (mkWorld (w_refs w)
                         (fun k => if PrimInt63.eqb k l
                                   then Some (existT _ A (tag, (nil, false)))
                                   else w_chans w k)
                         (w_maps w) (PrimInt63.add l 1%uint63)).
(** Buffering is idealised away in the proof model (capacity has no denotation
    here — only the FIFO + closed flag), so a buffered channel is created exactly
    like an unbuffered one; the capacity [n] survives only in the plugin lowering
    ([make(chan T, n)]). *)
Definition make_chan_buf {A : Type} (tag : GoTypeTag A) (n : int) : IO (GoChan A) :=
  make_chan tag.
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
    (consistent, non-degenerate), and the channel LAWS below are now THEOREMS
    derived from it — not free-standing axioms asserted on intuition.

    BLOCKING is idealised away (like divergence / OOM, and matching [run_io]'s
    totality): a [recv] equation is given only when the buffer is non-empty (or
    the channel is closed); a [recv] on a permanently-empty open channel blocks
    forever, which has no denotation here — a deadlock, out of scope.  This is the
    SEQUENTIAL (single-goroutine, or correctly-synchronised) slice; the
    cross-goroutine HAPPENS-BEFORE partial order is the next layer. *)
(** The channel STATE accessors/updates are now DEFINITIONS over [w_chans] (no
    longer axioms).  Because [GoChan A] carries no [GoTypeTag] (that would make
    [GoTypeTag] universe-inconsistent), the typed accessors take the element [tag]
    explicitly; it coerces the cell's stored buffer ([list E]) to the accessor's
    view ([list A]) — they are equal by construction, [tag_eq] recovers the proof.
    [chan_closed] needs no tag (it reads the bool directly). *)
Definition chan_buf {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : list A :=
  match w_chans w (ch_loc ch) with
  | Some (existT _ E (etag, (buf, _))) =>
      match tag_eq tag etag with
      | Some p => eq_rect E (fun X : Type => list X) buf A (eq_sym p)
      | None   => nil
      end
  | None => nil
  end.
Definition chan_closed {A : Type} (ch : GoChan A) (w : World) : bool :=
  match w_chans w (ch_loc ch) with
  | Some (existT _ _ (_, (_, cl))) => cl
  | None => false
  end.
(** Write a channel cell at [ch]'s location, tagged with [tag]. *)
Definition chan_write {A : Type} (tag : GoTypeTag A) (ch : GoChan A)
                      (buf : list A) (cl : bool) (w : World) : World :=
  mkWorld (w_refs w)
          (fun k => if PrimInt63.eqb k (ch_loc ch)
                    then Some (existT _ A (tag, (buf, cl)))
                    else w_chans w k)
          (w_maps w) (w_next w).
Definition chan_send_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World) : World :=
  chan_write tag ch (chan_buf tag ch w ++ (v :: nil)) (chan_closed ch w) w.
Definition chan_recv_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : World :=
  chan_write tag ch (tl (chan_buf tag ch w)) (chan_closed ch w) w.
Definition chan_close_upd {A : Type} (tag : GoTypeTag A) (ch : GoChan A) (w : World) : World :=
  chan_write tag ch (chan_buf tag ch w) true w.

(** Reading back what [chan_write] wrote (with the SAME tag) — the heap-cell
    round-trip, via [eqb_refl] (location hit) + [tag_eq_refl] (coercion identity). *)
Lemma chan_buf_write_same : forall {A} (tag : GoTypeTag A) ch buf cl w,
  chan_buf tag ch (chan_write tag ch buf cl w) = buf.
Proof.
  intros A tag ch buf cl w. unfold chan_buf, chan_write. cbn.
  rewrite (Uint63.eqb_refl (ch_loc ch)), tag_eq_refl. reflexivity.
Qed.
Lemma chan_closed_write_same : forall {A} (tag : GoTypeTag A) ch buf cl w,
  chan_closed ch (chan_write tag ch buf cl w) = cl.
Proof.
  intros A tag ch buf cl w. unfold chan_closed, chan_write. cbn.
  rewrite (Uint63.eqb_refl (ch_loc ch)). reflexivity.
Qed.
(** A write to [ch] leaves a DIFFERENT channel's cell ([ch']) untouched — record
    injectivity ([ch <> ch' => ch_loc ch <> ch_loc ch']) + [eqb_false_complete]. *)
Lemma chan_loc_neq : forall {A} (ch ch' : GoChan A), ch <> ch' -> ch_loc ch <> ch_loc ch'.
Proof.
  intros A ch ch' Hne Hloc. apply Hne.
  destruct ch as [l]; destruct ch' as [l']; cbn in Hloc; subst; reflexivity.
Qed.
Lemma chan_read_write_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) buf cl w,
  ch <> ch' -> w_chans (chan_write tag ch buf cl w) (ch_loc ch') = w_chans w (ch_loc ch').
Proof.
  intros A tag ch ch' buf cl w Hne. unfold chan_write. cbn.
  rewrite (Uint63.eqb_false_complete (ch_loc ch') (ch_loc ch)).
  - reflexivity.
  - intro H. apply (chan_loc_neq ch ch' Hne). symmetry; exact H.
Qed.

(** Heap-interface laws — now THEOREMS (were axioms): how [chan_buf]/[chan_closed]
    read after each update. *)
Theorem chan_buf_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_buf tag ch (chan_send_upd tag ch v w) = chan_buf tag ch w ++ (v :: nil).
Proof. intros. unfold chan_send_upd. rewrite chan_buf_write_same. reflexivity. Qed.
Theorem chan_buf_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (rest : list A) (w : World),
  chan_buf tag ch w = v :: rest -> chan_buf tag ch (chan_recv_upd tag ch w) = rest.
Proof. intros A tag ch v rest w H. unfold chan_recv_upd. rewrite chan_buf_write_same, H. reflexivity. Qed.
Theorem chan_closed_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch (chan_send_upd tag ch v w) = chan_closed ch w.
Proof. intros. unfold chan_send_upd. rewrite chan_closed_write_same. reflexivity. Qed.
Theorem chan_closed_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch (chan_recv_upd tag ch w) = chan_closed ch w.
Proof. intros. unfold chan_recv_upd. rewrite chan_closed_write_same. reflexivity. Qed.
Theorem chan_closed_close : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch (chan_close_upd tag ch w) = true.
Proof. intros. unfold chan_close_upd. rewrite chan_closed_write_same. reflexivity. Qed.

(** Channel SEPARATION (frame) — now THEOREMS: a send/receive on one channel leaves
    every OTHER channel's buffer untouched (distinct cells are independent). *)
Theorem chan_buf_send_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (v : A) (w : World),
  ch <> ch' -> chan_buf tag ch' (chan_send_upd tag ch v w) = chan_buf tag ch' w.
Proof.
  intros A tag ch ch' v w Hne. unfold chan_send_upd, chan_buf.
  rewrite (chan_read_write_frame tag ch ch' _ _ w Hne). reflexivity.
Qed.
Theorem chan_buf_recv_frame : forall {A} (tag : GoTypeTag A) (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_buf tag ch' (chan_recv_upd tag ch w) = chan_buf tag ch' w.
Proof.
  intros A tag ch ch' w Hne. unfold chan_recv_upd, chan_buf.
  rewrite (chan_read_write_frame tag ch ch' _ _ w Hne). reflexivity.
Qed.


(** The channel OPERATIONS, DEFINED over the state above.  Extraction lowers each by
    NAME to Go (the bodies — which mention the proof-only state — are suppressed).
    BLOCKING is idealised away (like [run_io] totality): a [recv]/[recv_ok]/[select]
    on an empty OPEN channel returns the zero/default rather than blocking — no proof
    depends on that case (the laws below cover only the non-empty / closed cases). *)
Definition send {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) : IO unit :=
  fun w => if chan_closed ch w then OPanic (any tt) w else ORet tt (chan_send_upd tag ch v w).
Definition recv {A} (tag : GoTypeTag A) (ch : GoChan A) : IO A :=
  fun w => match chan_buf tag ch w with
           | v :: _ => ORet v (chan_recv_upd tag ch w)
           | nil    => ORet (zero_val tag) w
           end.
Definition close_chan {A} (tag : GoTypeTag A) (ch : GoChan A) : IO unit :=
  fun w => if chan_closed ch w then OPanic (any tt) w else ORet tt (chan_close_upd tag ch w).
Definition recv_ok {A B} (tag : GoTypeTag A) (ch : GoChan A) (f : A -> bool -> IO B) : IO B :=
  fun w => match chan_buf tag ch w with
           | v :: _ => f v true (chan_recv_upd tag ch w)
           | nil    => f (zero_val tag) false w
           end.
Definition select_recv2 {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => match chan_buf tb ch2 w with
                       | v :: _ => k2 v (chan_recv_upd tb ch2 w)
                       | nil    => k1 (zero_val ta) w
                       end
           end.
Definition select_recv_default {A C} (ta : GoTypeTag A) (ch1 : GoChan A)
                                      (k1 : A -> IO C) (d : IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => d w
           end.
(** [go_spawn m] (Go spec "Go statements"): the SEQUENTIAL approximation — run [m] to completion, keep its world
    effect, return.  Faithful concurrency lives in the calculus (concurrency.v); this is
    holdout #2 (ZERO_AXIOMS_PLAN.md).  No law constrains it; the definition is total. *)
Definition go_spawn (m : IO unit) : IO unit :=
  fun w => ORet tt (match m w with ORet _ w' => w' | OPanic _ w' => w' end).

(** The [run_*] laws are now THEOREMS, conditioned on channel state.  [send]/
    [recv]/[close_chan] carry the element [tag] (the typed-heap accessors need it
    since [GoChan] is tag-free). *)
Lemma run_send : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false ->
  run_io (send tag ch v) w = ORet tt (chan_send_upd tag ch v w).
Proof. intros A tag ch v w H. unfold send, run_io. rewrite H. reflexivity. Qed.
Lemma run_send_closed : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = true ->
  run_io (send tag ch v) w = OPanic (any tt) w.
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
Proof. intros A B tag ch f w H _. unfold recv_ok, run_io. rewrite H. reflexivity. Qed.
Lemma run_close : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch w = false ->
  run_io (close_chan tag ch) w = ORet tt (chan_close_upd tag ch w).
Proof. intros A tag ch w H. unfold close_chan, run_io. rewrite H. reflexivity. Qed.
Lemma run_close_closed : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch w = true ->
  run_io (close_chan tag ch) w = OPanic (any tt) w.
Proof. intros A tag ch w H. unfold close_chan, run_io. rewrite H. reflexivity. Qed.

(** ---- The channel laws, now DERIVED as theorems ---- *)

(** After [send ch v] into an OPEN, EMPTY channel, the next [recv] returns [v].
    (Honest conditions the old unconditional axiom hid: send must not panic on a
    closed channel, and FIFO means [recv] returns [v] only when [v] is at the
    head — i.e. the buffer was empty before the send.) *)
Theorem send_recv : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false -> chan_buf tag ch w = nil ->
  run_io (bind (send tag ch v) (fun _ => recv tag ch)) w
  = ORet v (chan_recv_upd tag ch (chan_send_upd tag ch v w)).
Proof.
  intros A tag ch v w Hclosed Hempty.
  rewrite run_bind, (run_send tag ch v w Hclosed). cbn.
  apply (run_recv tag ch v nil).
  rewrite chan_buf_send, Hempty. reflexivity.
Qed.

(** [recv_ok] variant: after [send ch v] into an open, empty channel, [recv_ok]
    delivers [(v, true)] and runs the continuation in the dequeued world. *)
Theorem send_recv_ok : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A)
    (f : A -> bool -> IO B) (w : World),
  chan_closed ch w = false -> chan_buf tag ch w = nil ->
  run_io (bind (send tag ch v) (fun _ => recv_ok tag ch f)) w
  = run_io (f v true) (chan_recv_upd tag ch (chan_send_upd tag ch v w)).
Proof.
  intros A B tag ch v f w Hclosed Hempty.
  rewrite run_bind, (run_send tag ch v w Hclosed). cbn.
  apply (run_recv_ok tag ch f v nil).
  rewrite chan_buf_send, Hempty. reflexivity.
Qed.

(** Sending on a closed channel panics (Go spec): close then send → panic. *)
Theorem send_closed_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => send tag ch v)) w
  = OPanic (any tt) (chan_close_upd tag ch w).
Proof.
  intros A tag ch v w Hopen.
  rewrite run_bind, (run_close tag ch w Hopen). cbn.
  exact (run_send_closed tag ch v (chan_close_upd tag ch w) (chan_closed_close tag ch w)).
Qed.

(** Closing an already-closed channel panics (Go spec): close then close → panic. *)
Theorem double_close_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => close_chan tag ch)) w
  = OPanic (any tt) (chan_close_upd tag ch w).
Proof.
  intros A tag ch w Hopen.
  rewrite run_bind, (run_close tag ch w Hopen). cbn.
  exact (run_close_closed tag ch (chan_close_upd tag ch w) (chan_closed_close tag ch w)).
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

(** ---- Phase 4a: the 4th go-mem channel rule — close ⤳ a receive returning zero ----

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

(** ---- Phase 4b: the goroutine FORK edge ----

    go-mem: "the go statement that starts a new goroutine is synchronized before the
    start of the goroutine's execution."  So a value the parent writes BEFORE the
    [go] is visible to the child with NO channel — the fork alone orders it.  The
    canonical case (parent writes [x] then spawns a child that reads [x]) is
    whole-program race-free purely by the fork edge.  (Reuses the generic
    [Race]/[RaceFree]/[racefree_of_ordered] from Phase 3 — axiom-free.) *)
Inductive ForkEvent := PWrite | PGo | CStartE | CRead.
Inductive fork_hb : ForkEvent -> ForkEvent -> Prop :=
  | fk_po_parent : fork_hb PWrite PGo        (* parent: write x, then go *)
  | fk_fork      : fork_hb PGo CStartE        (* go ⤳ child's start *)
  | fk_po_child  : fork_hb CStartE CRead       (* child: start, then read x *)
  | fk_trans : forall a b c, fork_hb a b -> fork_hb b c -> fork_hb a c.
Definition fork_acc (e : ForkEvent) : Access :=
  match e with PWrite => AWrite 0 | CRead => ARead 0 | _ => ARead 1 end.  (* x = location 0 *)
Definition fork_gid (e : ForkEvent) : nat :=
  match e with PWrite => 0 | PGo => 0 | CStartE => 1 | CRead => 1 end.
Theorem fork_write_before_read : fork_hb PWrite CRead.
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

(* [GoInt] is now [int]; [len] counts elements (lowered to Go [len] — body suppressed). *)
Fixpoint len {A} (xs : GoSlice A) : GoInt :=
  match xs with nil => 0%uint63 | _ :: r => PrimInt63.add 1%uint63 (len r) end.
Definition cap {A} (xs : GoSlice A) : GoInt := len xs.   (* model: cap = len *)
Definition append {A} (xs ys : GoSlice A) : GoSlice A := xs ++ ys.   (* GoSlice A = list A *)

(** [min]/[max] (Go 1.21 predeclared builtins) on [int] — the smaller / larger of
    two values, by the SIGNED ordering (Go's int [<]), so [go_min] = Go [min(a,b)]
    and [go_max] = Go [max(a,b)] for the [int] type.  Computable (so [go_min 3 5 =
    3] is a THEOREM); the plugin lowers the call to Go's builtin.  (Go's [min]/[max]
    also apply to floats — with NaN/`-0` corner cases — and strings; those follow
    once those orderings are settled.) *)
Definition go_min (a b : int) : int := if Sint63.ltb a b then a else b.
Definition go_max (a b : int) : int := if Sint63.ltb a b then b else a.

(** Construct a typed Go slice from a Rocq list literal.
    The [GoTypeTag] witness lets the plugin emit [[]T{v1, v2, ...}] with the
    correct element type instead of falling back to [append(nil, ...)]. *)
Definition slice_of_list {A} (_ : GoTypeTag A) (xs : list A) : GoSlice A := xs.

(** [make([]T, n)] — a fresh slice of [n] zero values (Go's [make] for slices).
    Modelled as [repeat (zero_val tag) n] (so [len] is [n], every element the zero
    value) — a freshly-allocated slice, hence no aliasing concern.  The plugin
    lowers it to Go [make([]T, n)] (element type from the tag, [n] the length).
    (The 3-arg [make([]T, len, cap)] and [copy] involve the backing-array /
    aliasing model — tracked separately, Tier 3 #8a.) *)
Definition slice_make {A : Type} (tag : GoTypeTag A) (n : nat) : GoSlice A :=
  List.repeat (zero_val tag) n.

(** Indexed access (Go spec "Index expressions") — returns [IO A] because Go panics on out-of-bounds.

    ESCAPE HATCH: the raw panicking form; use inside [catch] to handle OOB.
    Prefer [slice_at_ok] (below), the safe-by-construction default.  A
    proof-carrying [slice_at xs i (i < len xs)] → [xs[i]] unguarded is still a
    tracked gap (needs the int model, CLAUDE.md "Known gaps").

    DEFINITION (not an axiom): [GoSlice A = list A], so the read is the i'th
    element; out of bounds (incl. a negative index) PANICS, like Go.  The plugin
    lowers a call BY NAME to [xs[i]] (the body is suppressed and [Extraction
    NoInline]'d), so this body affects only PROOFS, never the emitted Go — AND it
    must pull in NO external stdlib function (those would enter the extraction
    closure and leak), so the lookup is the SELF-CONTAINED, [int]-indexed
    [go_list_nth] (structural on the list, suppressed) rather than
    [nth_error]+[Z.to_nat].  The signed guard [0 <= i < len xs] decides in-range;
    in range ⇒ the element, else ⇒ panic. *)
Fixpoint go_list_nth {A : Type} (xs : list A) (i : int) (d : A) : A :=
  match xs with
  | nil        => d
  | x :: rest  => if PrimInt63.eqb i 0%uint63 then x
                  else go_list_nth rest (PrimInt63.sub i 1%uint63) d
  end.
Definition slice_get {A : Type} (tag : GoTypeTag A) (xs : GoSlice A) (i : int) : IO A :=
  fun w => if (Sint63.leb 0 i && Sint63.ltb i (len xs))%bool
           then ORet (go_list_nth xs i (zero_val tag)) w
           else OPanic (any tt) w.   (* out of bounds / negative: Go panics *)

(** Safe checked index (the safe-by-construction default for slice access).
    [slice_at_ok tag xs i (fun v ok => body)] bounds-checks [i]: if it is in
    range then [v = xs[i]] and [ok = true]; otherwise [v] is the zero value and
    [ok = false].  CPS like [recv_ok]; because the caller must handle [ok =
    false], this form cannot panic out of bounds.  [i : int] is SIGNED (Sint63),
    so the check covers BOTH ends ([0 <= i < len]); a negative index is in range
    for Go's panic, so it must yield [ok = false], not slip through.

    DEFINITION (not an axiom): bounds-check the SIGNED index, then read via the
    self-contained [go_list_nth] (no stdlib dep, same reason as [slice_get]); in
    range ⇒ [k v true], else ⇒ [k zero false].  Lowered BY NAME (body suppressed
    + NoInline), so it affects only proofs. *)
Definition slice_at_ok {A B : Type}
  (tag : GoTypeTag A) (xs : GoSlice A) (i : int) (k : A -> bool -> IO B) : IO B :=
  if (Sint63.leb 0 i && Sint63.ltb i (len xs))%bool
  then k (go_list_nth xs i (zero_val tag)) true
  else k (zero_val tag) false.

(** ---- String operations (Go spec "String types") ----

    [str_len s] is the BYTE length (Go [len(s)]): a computable [int] that counts
    the [string]'s bytes, so [str_len "Go" = 2] is a THEOREM.  The plugin lowers
    it to Go [int64(len(s))] — the byte count in the [int] (Sint63/int64) model.

    [str_at_ok] is the SAFE byte index (spec: "a string's bytes can be accessed
    by integer indices [0 <= i < len(s)]"; [s[i]] is of type [byte]).  CPS /
    comma-ok like [slice_at_ok]: it FORCES handling the out-of-range case, so it
    cannot panic.  In range ⇒ [b = s[i]] (the byte, a [GoByte] = [uint8]) and
    [ok = true]; else [b = 0], [ok = false].  [i : int] is SIGNED, so the bounds
    check covers BOTH ends.  Lowers to a bounds-checked [int64(s[i])] (the byte
    in the int64 carrier), mirroring [slice_at_ok].

    [str_concat] is Go's string [+] (spec "Operators": string concatenation) — a
    pure, total operation on immutable byte sequences, so [str_concat "ab" "cd" =
    "abcd"] is a THEOREM.  Defined by its OWN recursion (no [String.append]
    dependency to drag into extraction); suppressed in the plugin, lowered to Go
    [a + b]. *)
Fixpoint str_len (s : GoString) : int :=
  match s with
  | EmptyString   => 0%uint63
  | String _ rest => PrimInt63.add 1%uint63 (str_len rest)
  end.

(** DEFINITION (not an axiom): the i'th BYTE of the string at the signed index,
    as a [GoByte] (= [GoU8]); out of range ⇒ [k 0 false].  Like the slice forms,
    the body must pull in NO external stdlib function, so it uses SELF-CONTAINED,
    suppressed helpers: [ascii_byte] decodes the 8 bits of an [ascii] to its 0–255
    [GoU8] carrier INLINE (no [nat_of_ascii], which drags in [N_of_digits]), and
    [go_str_byte] walks to the i'th byte ([int]-indexed, structural on the string,
    no [String.get]+[Z.to_nat]).  Lowered BY NAME to a bounds-checked [int64(s[i])]
    (body suppressed + NoInline), so this affects only proofs. *)
Definition ascii_byte (c : ascii) : GoByte :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      let v (b : bool) (k : int) : int := if b then k else 0%uint63 in
      MkU8 (PrimInt63.add (v b0 1%uint63)
           (PrimInt63.add (v b1 2%uint63)
           (PrimInt63.add (v b2 4%uint63)
           (PrimInt63.add (v b3 8%uint63)
           (PrimInt63.add (v b4 16%uint63)
           (PrimInt63.add (v b5 32%uint63)
           (PrimInt63.add (v b6 64%uint63) (v b7 128%uint63))))))))
  end.
Fixpoint go_str_byte (s : GoString) (i : int) : GoByte :=
  match s with
  | EmptyString  => MkU8 0
  | String c rest => if PrimInt63.eqb i 0%uint63 then ascii_byte c
                     else go_str_byte rest (PrimInt63.sub i 1%uint63)
  end.
Definition str_at_ok {B : Type}
  (s : GoString) (i : int) (k : GoByte -> bool -> IO B) : IO B :=
  if (Sint63.leb 0 i && Sint63.ltb i (str_len s))%bool
  then k (go_str_byte s i) true
  else k (MkU8 0) false.

Fixpoint str_concat (a b : GoString) : GoString :=
  match a with
  | EmptyString   => b
  | String c rest => String c (str_concat rest b)
  end.

(** ---- Mutable local variables (Go spec "Variables" / "Assignment statements") ----

    [Ref A] is a mutable cell holding an [A] — Go's mutable local variable.
    Pure [let]-binding is single-assignment and cannot express a value that
    *changes* (a loop counter, an accumulator updated in place); a [Ref] can.
    [ref_new tag v] declares the variable ([x := v]); [ref_get] reads it;
    [ref_set] assigns ([x = v]).  A local cell extracts to a plain Go variable;
    cross-function sharing (pointers, [*T]) is a later, separate step.

    [Ref A] is now a CONCRETE typed-cell HANDLE (no longer an axiom): a location
    [r_loc] into the world's [w_refs] heap, plus the element [GoTypeTag] [r_tag]
    (so a read can coerce the stored cell back to [A]).  The OPERATIONS are
    DEFINITIONS over the heap and [ref_sel_upd_same] (read-after-write) is now a
    THEOREM.  At extraction a [Ref A] is a plain Go variable — [ref_new] lowers to
    [x := v], [ref_get] to a read, [ref_set] to [x = v] — and the [r_loc]/[r_tag]
    fields and the heap are proof-only (erased). *)
Record Ref (A : Type) : Type := mkRef { r_loc : int ; r_tag : GoTypeTag A }.
Arguments mkRef {A} _ _.
Arguments r_loc {A} _.
Arguments r_tag {A} _.

(** [ref_sel r w]: read [r]'s cell from [w_refs] and coerce it to [A] via the
    ref's tag.  A well-typed program always reads the cell it wrote, so the stored
    tag matches [r_tag] and the coercion succeeds; the mismatch / empty-cell cases
    default to the type's zero value (totality). *)
Definition ref_sel {A : Type} (r : Ref A) (w : World) : A :=
  match w_refs w (r_loc r) with
  | Some (existT _ _ (tag0, x0)) =>
      match tag_coerce (r_tag r) tag0 x0 with
      | Some a => a
      | None   => zero_val (r_tag r)
      end
  | None => zero_val (r_tag r)
  end.

(** [ref_upd r v w]: write [v] (tagged with [r]'s own tag) at [r]'s location. *)
Definition ref_upd {A : Type} (r : Ref A) (v : A) (w : World) : World :=
  mkWorld (fun l => if PrimInt63.eqb l (r_loc r)
                    then Some (existT _ A (r_tag r, v))
                    else w_refs w l)
          (w_chans w) (w_maps w) (w_next w).

(** [ref_new tag v]: allocate the fresh location [w_next], seed [r_tag := tag],
    write [v], bump the allocator.  Carries the [GoTypeTag] so the cell is tagged
    (lowers to [x := v]; the tag and location are erased). *)
Definition ref_new {A : Type} (tag : GoTypeTag A) (v : A) : IO (Ref A) :=
  fun w => let l := w_next w in
           ORet (mkRef l tag)
                (mkWorld (fun k => if PrimInt63.eqb k l
                                   then Some (existT _ A (tag, v))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (PrimInt63.add l 1%uint63)).
(* [ref_get] carries a [GoTypeTag] so that, when a read is bound inside a loop
   block, the lowering knows the Go type to hoist its declaration. *)
Definition ref_get {A} (tag : GoTypeTag A) (r : Ref A) : IO A :=
  fun w => ORet (ref_sel r w) w.
Definition ref_set {A} (r : Ref A) (v : A) : IO unit :=
  fun w => ORet tt (ref_upd r v w).
Lemma run_ref_get : forall {A} (tag : GoTypeTag A) (r : Ref A) (w : World),
  run_io (ref_get tag r) w = ORet (ref_sel r w) w.
Proof. reflexivity. Qed.
Lemma run_ref_set : forall {A} (r : Ref A) (v : A) (w : World),
  run_io (ref_set r v) w = ORet tt (ref_upd r v w).
Proof. reflexivity. Qed.

(** Read-after-write at the STATE level — now a THEOREM (was an axiom): [ref_upd]
    tags the cell with [r]'s own tag, so the subsequent [ref_sel]'s [tag_coerce]
    is reflexive ([tag_coerce_refl]) and the location lookup hits ([eqb_refl]). *)
Lemma ref_sel_upd_same : forall {A} (r : Ref A) (v : A) (w : World),
  ref_sel r (ref_upd r v w) = v.
Proof.
  intros A r v w. unfold ref_sel, ref_upd. cbn.
  rewrite (Uint63.eqb_refl (r_loc r)).
  rewrite tag_coerce_refl. reflexivity.
Qed.

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

(** ---- Control flow as a CFG (the goto model)
    (Go spec "If statements" / "For statements" / "Goto statements" / "Return statements") ----

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
    [Jump] targets are emitted, since Go rejects unused labels).

    Now a DEFINITION (not an axiom).  This is the ONE genuinely non-terminating
    combinator — a backward [Jump] is an unbounded loop — so a TOTAL Coq function
    must idealise divergence away, exactly as [run_io] is total (OOM / divergence
    are out of scope by decision).  We do so with FUEL: [run_blocks_fuel] follows
    [Jump]s up to [block_fuel] steps, treating exhaustion as [Done].  This affects
    only PROOFS: the plugin lowers [run_blocks] BY NAME to Go labels + [goto] (the
    real, unbounded semantics), so the fuel never reaches the emitted Go, and no
    theorem constrains [run_blocks]'s computational behaviour. *)
Fixpoint block_nth (blocks : list (IO Next)) (n : nat) : IO Next :=
  match blocks, n with
  | b :: _,    O   => b
  | _ :: rest, S k => block_nth rest k
  | nil,       _   => ret Done
  end.
Fixpoint run_blocks_fuel (fuel start : nat) (blocks : list (IO Next)) : IO unit :=
  match fuel with
  | O   => ret tt
  | S f => bind (block_nth blocks start)
                (fun nx => match nx with
                           | Jump n => run_blocks_fuel f n blocks
                           | Done   => ret tt
                           end)
  end.
(** The divergence-idealisation cap (proof-only; never computed nor extracted). *)
Definition block_fuel : nat := 1000.
Definition run_blocks (start : nat) (blocks : list (IO Next)) : IO unit :=
  run_blocks_fuel block_fuel start blocks.

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

(** [Sess i j A] is now a DEFINITION, not an axiom — a single-field record
    wrapping an [IO A], INDEXED (as rigid inductive parameters) by the protocol
    states [i], [j].  Rigidity is essential: a bare alias [Sess i j A := IO A]
    would make [Sess i1 j1 A] and [Sess i2 j2 A] CONVERTIBLE (both reduce to
    [IO A]), so a wrong-protocol value would type-check and the [Fail] linearity
    tests would no longer fail.  As an inductive, the indices are part of the
    type's identity, so protocol mismatches stay TYPE ERRORS.  The single [IO A]
    field erases (Coq unboxes a one-field record), and the phantom [i]/[j]
    parameters never appear in it, so [Sess i j A] lowers exactly like [IO A] —
    the plugin lowers the session OPERATIONS by name (channel passing). *)
Record Sess (i j : Proto) (A : Type) : Type := MkSess { run_sess : IO A }.
Arguments MkSess {i j A} _.
Arguments run_sess {i j A} _.

(** Pure value; protocol state unchanged.  Lowers like [ret]. *)
Definition sret {P : Proto} {A : Type} (x : A) : Sess P P A := MkSess (ret x).

(** Sequence: [m] advances [i→j], then [k a] advances [j→k].  Lowers like
    [bind] (sequential Go statements). *)
Definition sbind {P Q R : Proto} {A B : Type}
  (m : Sess P Q A) (k : A -> Sess Q R B) : Sess P R B :=
  MkSess (bind (run_sess m) (fun a => run_sess (k a))).

(** Send: consumes the head [PSend A] step.  No endpoint argument — the channel
    is implicit, supplied by the enclosing [run_session].
    Lowers to [_sess_ch <- any(v)]. *)
Definition ssend {A : Type} {P : Proto} (v : A) : Sess (PSend A P) P unit :=
  MkSess (ret tt).

(** Receive: consumes the head [PRecv A] step, yielding the received value.
    Lowers to [_r := <-_sess_ch; _r.(T)].  The proof-model body returns the type's
    zero value (the channel effect lives in the plugin lowering, idealised away
    here just as the old axiom had no denotation). *)
Definition srecv {A : Type} {P : Proto} (tag : GoTypeTag A) : Sess (PRecv A P) P A :=
  MkSess (ret (zero_val tag)).

(** Lift an [IO] action into a session at any protocol state (consumes no
    protocol step) — e.g. to print a received value.  Lowers to the IO body. *)
Definition slift {P : Proto} {A : Type} (m : IO A) : Sess P P A := MkSess m.

(** Session sequencing notations (the [sbind] analogues of [>>'] / [<-' ;;]):
    [>>>] discards the step's result, [<<- … ;;;] binds it.  Right-associative so
    [a >>> b >>> c] is the natural right-nested [sbind a (fun _ => sbind b …)]
    that the protocol indices and the plugin's session lowering expect. *)
Notation "m >>> k" := (sbind m (fun _ => k))
  (at level 80, right associativity).
Notation "x <<- m ;;; k" := (sbind m (fun x => k))
  (at level 80, m at level 90, right associativity).

(** Run two complementary roles concurrently: the client realises [P] to
    completion, the server realises [dual P].  Allocates one shared channel,
    spawns the server, runs the client.
    Lowers to: [_sess_ch := make(chan any); go func(){ <server> }(); <client>]. *)
Definition run_session {P : Proto}
  (client : Sess P PEnd unit) (server : Sess (dual P) PEnd unit) : IO unit :=
  ret tt.
