(** ==================================================================================================
    GoRuntimeTypes — Go's runtime type layer: the carrier types the model addresses by TYPE
    ([GoString]/[GoSlice]/[GoChan]/[GoMap]/[Ptr]/[GoFunc], the recursive demo structs
    [ListNode]/[ChanBox]), the term-level type witness [GoTypeTag] with its decidable coercion
    [tag_eq], the boxed value [GoAny] (+ [any]/[anyt]), the [Tagged] inference class, and the
    per-type [zero_val].  Mined out of the frozen builtins.v monolith (plans/builtins-split.md
    wave 2); imports only the numeric model — nothing here touches [IO]/[World].
    ================================================================================================ *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
From Stdlib Require Import ZArith.
From Stdlib Require Import StrictProp.
From Fido Require Import GoNumeric.

(** Go's string type (Go spec "String types"): an immutable sequence of BYTES.
    Modelled as Coq's [string] (a sequence of [Ascii.ascii]), so [len] is the
    BYTE count and [s[i]] the i'th BYTE, exactly as the spec defines.
    Immutability is automatic (a pure value).  The plugin maps [string] → Go
    [string] and decodes literals to byte-faithful Go string literals.
    The rune view ([range s]) is a separate UTF-8 decode, deferred. *)
From Stdlib Require Import Strings.String Strings.Ascii.
Definition GoString : Type := string.

(** Go's slice type, modelled as [list A]; the plugin maps [list A] → [[]T].
    NOTE — aliasing: slices are reference types in Go.  The pure functional
    model (append returns a new list) is sound only for single-goroutine
    sequential programs with no aliasing of the underlying array; aliasing or
    concurrency requires [append] in [IO] (like [map_set]/[map_delete]). *)
Definition GoSlice (A : Type) : Type := list A.


(** [GoChan]/[GoMap] are CONCRETE phantom-LOCATION records: a [GoChan A] is a
    handle [{ ch_loc : nat }] into the world's channel state, the element type
    [A] carried only PHANTOM (in the type, never as a field).  Invariant: they
    do NOT carry their [GoTypeTag] — a tag field would make [GoTypeTag] (which
    references them via [TChan]/[TMap]) UNIVERSE-INCONSISTENT.  At extraction
    [GoChan A] → Go [chan T], [GoMap K V] → [map[K]V] (rendered by type NAME);
    the handle and record wrapper are erased. *)
Record GoChan (A : Type) : Type := MkChan { ch_loc : nat }.
Record GoMap  (K V : Type) : Type := MkMap { gm_loc : nat }.
Arguments MkChan {A} _.
Arguments ch_loc {A} _.
Arguments MkMap {K V} _.
Arguments gm_loc {K V} _.
(** [Ptr A] is a TAG-FREE phantom-LOCATION record (same universe reason as
    [GoChan]/[GoMap]).  The pointee's type lives in the world heap cell ([RefCell]
    stores the tag), so the deref ops ([ptr_get]/[ptr_set]/…) take the [GoTypeTag]
    explicitly.  Extraction: [Ptr A] → Go [*T]; the [p_loc] handle is erased. *)
Record Ptr (A : Type) : Type := mkPtr { p_loc : nat }.
Arguments mkPtr {A} _.
Arguments p_loc {A} _.

(** ---- Type assertions ----

    [GoTypeTag T] is a term-level witness encoding the Go type [T].
    Because it is an inductive (not a type), it survives extraction —
    the plugin inspects the constructor to emit [v.(T)] with the right type.

    Extend this inductive as new Go types are added to builtins. *)

(* A genuinely RECURSIVE Go struct type — [type ListNode struct { Val int64 ; Next *ListNode }].
   Defined above [GoTypeTag] so the tag inductive can carry the NULLARY nominal tag
   [TListNode : GoTypeTag ListNode].  Axiom-free because:
   (1) [Inductive] (the [Record] keyword forbids self-reference) with record-projection syntax —
       extraction still classifies it as a record ⇒ the plugin emits a Go [struct].  The recursion
       goes through the TAG-FREE phantom handle [Ptr ListNode] ⇒ vacuously positive, and
       [GoTypeTag ListNode] stays universe-consistent.
   (2) A NULLARY nominal tag does not structurally contain itself: [TListNode] is a base case like
       [TBool]; the [Next] field's tag is the FINITE term [TPtr TListNode], so the recursive TYPE
       round-trips through [tag_eq]. *)
Inductive ListNode := MkListNode { ln_val : GoI64 ; ln_next : Ptr ListNode }.

(* "CHANNELS THAT SEND THEMSELVES" — [type ChanBox struct { Id int64 ; Ch chan ChanBox }]: a
   [chan ChanBox] can carry a value whose [Ch] field IS that very channel.  Same construction as
   [ListNode], with the recursion through the tag-free [GoChan] ⇒ vacuously positive and
   [GoTypeTag ChanBox] universe-consistent; the nullary nominal tag [TChanBox] is finite, the
   channel-of-itself tag is [TChan TChanBox].  2 fields ⇒ not unboxed ⇒ emits the named Go struct. *)
Inductive ChanBox := MkChanBox { cb_id : GoI64 ; cb_chan : GoChan ChanBox }.

(** Go function VALUES are NULLABLE references — a [func] variable defaults to [nil] and CALLING
    a nil func PANICS (Go's nil-pointer dereference).  A total Coq [A -> B] cannot model that: it
    is always callable, so a "zero function" would be a fake callable inhabitant.  We
    therefore model a function value as [option (A -> B)]: [None] is the [nil] func, [Some f] a
    real closure.  The zero value is [None] (faithful), and invocation is the EFFECTFUL
    [gofunc_call] (defined once [panic] is in scope) which PANICS on [None].  This is the type the
    [TArrow] tag describes, so [zero_val (TArrow ..) = NilFunc] is a genuine nil — not callable.
    A DISTINCT inductive (not [option]) so extraction keeps it opaque — it renders as Go's native
    nilable [func(A) B] ([NilFunc]=nil, [SomeFunc f]=f), never the generic [option] lowering. *)
Inductive GoFunc (A B : Type) : Type :=
  | NilFunc  : GoFunc A B
  | SomeFunc : (A -> B) -> GoFunc A B.
Arguments NilFunc {A B}.
Arguments SomeFunc {A B} _.

Inductive GoTypeTag : Type -> Type :=
  | TBool    : GoTypeTag bool
  | TInt64   : GoTypeTag GoInt           (* platform int — DISTINCT Z-carried record; → Go [int] *)
  | TFloat64 : GoTypeTag GoFloat64        (* → float64 (spec_float) *)
  | TString  : GoTypeTag GoString
  | TU8  : GoTypeTag GoU8  | TI8  : GoTypeTag GoI8
  | TU16 : GoTypeTag GoU16 | TI16 : GoTypeTag GoI16
  | TU32 : GoTypeTag GoU32 | TI32 : GoTypeTag GoI32
  | TI64 : GoTypeTag GoI64               (* → int64 (full-width Z-carried signed) *)
  | TU64 : GoTypeTag GoU64               (* → uint64 (full-width Z-carried unsigned) *)
  | TUnit : GoTypeTag unit
  (* Go's platform-width [int]/[uint] — distinct Go types ([cap]/[len] return [GoInt]).
     [TUint] indexes the DISTINCT record [GoUint].  Invariant: ONE canonical tag AND one
     Rocq type per Go type — a non-injective tag→runtime-Go-type map would make [tag_eq]
     disagree with Go's [v.(T)]. *)
  (* [TInt64] is the ONE tag for Go's platform [int]; the fixed-width [int64]'s tag
     is [TI64] (the [GoI64] record). *)
  | TUint    : GoTypeTag GoUint
  | TFloat32 : GoTypeTag GoFloat32
  (* RECURSIVE / self-referential struct [ListNode] (above) — a NULLARY nominal tag, the crack of
     the recursive-type-tag wall.  It does NOT structurally contain itself (unlike a hypothetical
     [tag = TPtr tag]), so the inductive stays FINITE; the [Next : *ListNode] field's tag is the
     finite term [TPtr TListNode].  This is what lets a [*ListNode] cell live in the typed heap
     ([ptr_new]/[ptr_get] take [TListNode]) so a multi-node list is genuinely allocatable + traversable. *)
  | TListNode : GoTypeTag ListNode
  (* RECURSIVE through a CHANNEL — [ChanBox] (above), the "channel that sends itself" type.  Another
     nullary nominal tag (finite, like [TListNode]); the channel-of-itself tag is the finite [TChan
     TChanBox], so a [chan ChanBox] is makeable + send/recv-able. *)
  | TChanBox : GoTypeTag ChanBox
  (* Composite type tags — carry the element/key/value tags so the plugin can
     reconstruct the full Go type string recursively. *)
  | TChan  : forall {A : Type},           GoTypeTag A -> GoTypeTag (GoChan A)
  | TSlice : forall {A : Type},           GoTypeTag A -> GoTypeTag (GoSlice A)
  | TMap   : forall {K V : Type}, GoTypeTag K -> GoTypeTag V -> GoTypeTag (GoMap K V)
  (* function type — lets a DEFINED TYPE over a func underlying ([type Handler func(A) B])
     carry the GoTypeTag phantom that stops Coq unboxing its single value field.  Arrows are
     never decided equal by [tag_eq] (the catch-all returns [None]) — fine, a func type is
     not a map key nor type-switched. *)
  | TArrow : forall {A B : Type}, GoTypeTag A -> GoTypeTag B -> GoTypeTag (GoFunc A B)
  (* product (pair) type — the SOUND backing for struct channels: unlike a nominal struct,
     [A * B] is CANONICAL, so [tag_eq] can recover [A1*B1 = A2*B2] from the component tags.
     A 2-field struct is modelled as a product (marshalled via its StructRep iso) yet still
     EXTRACTS to its native named Go struct — methods/embedding intact. *)
  | TProd : forall {A B : Type}, GoTypeTag A -> GoTypeTag B -> GoTypeTag (A * B)
  (* pointer type [*T] — a tag-free [Ptr A] handle (defined above, like [GoChan]); the element tag is
     recovered by [tag_eq] so a [*T] can be a channel payload / [any] box / map value.  [==] on
     pointers compares the location (Go compares addresses). *)
  | TPtr : forall {A : Type}, GoTypeTag A -> GoTypeTag (Ptr A).

(** TRANSPARENT congruences for the CONCRETE [GoChan]/[GoMap] records, forced
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
Definition gofunc_cong {A A' B B'} (p : A = A') (q : B = B')
  : @eq Type (GoFunc A B) (GoFunc A' B') :=
  match p in (_ = A2), q in (_ = B2) return (@eq Type (GoFunc A B) (GoFunc A2 B2)) with
  | eq_refl, eq_refl => eq_refl
  end.
Definition goprod_cong {A A' B B' : Type} (p : A = A') (q : B = B')
  : @eq Type (A * B)%type (A' * B')%type :=
  match p in (_ = A2), q in (_ = B2) return (@eq Type (A * B)%type (A2 * B2)%type) with
  | eq_refl, eq_refl => eq_refl
  end.
Definition goptr_cong {A A'} (p : A = A') : @eq Type (Ptr A) (Ptr A') :=
  match p in (_ = X) return (@eq Type (Ptr A) (Ptr X)) with eq_refl => eq_refl end.

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
  | TU64, TU64 => Some eq_refl
  | TUnit, TUnit => Some eq_refl
  | TUint, TUint       => Some eq_refl
  | TFloat32, TFloat32 => Some eq_refl
  | TListNode, TListNode => Some eq_refl   (* recursive nominal type decides equal to itself — the heap read-after-write at [*ListNode] *)
  | TChanBox, TChanBox => Some eq_refl     (* recursive-through-channel nominal type — the channel read-after-write at [chan ChanBox] *)
  | TChan a, TChan b   => match tag_eq a b with Some p => Some (gochan_cong p) | None => None end
  | TSlice a, TSlice b => match tag_eq a b with Some p => Some (f_equal GoSlice p) | None => None end
  | TMap ka va, TMap kb vb =>
      match tag_eq ka kb, tag_eq va vb with
      | Some p, Some q => Some (gomap_cong p q)
      | _, _ => None
      end
  | TArrow a1 b1, TArrow a2 b2 =>
      match tag_eq a1 a2, tag_eq b1 b2 with
      | Some p, Some q => Some (gofunc_cong p q)
      | _, _ => None
      end
  | TProd a1 b1, TProd a2 b2 =>
      match tag_eq a1 a2, tag_eq b1 b2 with
      | Some p, Some q => Some (goprod_cong p q)
      | _, _ => None
      end
  | TPtr a, TPtr b     => match tag_eq a b with Some p => Some (goptr_cong p) | None => None end
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
  - rewrite IHt1, IHt2; reflexivity.                (* TArrow (gofunc_cong reduces) *)
  - rewrite IHt1, IHt2; reflexivity.                (* TProd (goprod_cong reduces) *)
  - rewrite IHt; reflexivity.                       (* TPtr (goptr_cong reduces) *)
Qed.

(** [tag_coerce t t x = Some x]: coercing along a tag's reflexive match is the
    identity (from [tag_eq_refl]). *)
Lemma tag_coerce_refl : forall {A} (t : GoTypeTag A) (x : A), tag_coerce t t x = Some x.
Proof. intros A t x. unfold tag_coerce. rewrite tag_eq_refl. reflexivity. Qed.

(** [TProd] soundness — the foundation for struct channels.  [tag_eq] RECOVERS the product
    type-equality (so a heterogeneous channel cell can cast a stored pair back to the
    accessor's type), the very property a NOMINAL struct tag cannot provide.  This is exactly
    why a struct channel is modelled product-backed: [A * B] is canonical, [Point] is not. *)
Example tprod_tag_sound : tag_eq (TProd TI64 TBool) (TProd TI64 TBool) = Some eq_refl.
Proof. reflexivity. Qed.

(** RECURSIVE type-tag soundness — the crack of the self-referential-type wall.  The recursive
    nominal type [ListNode] gets a FINITE tag [TListNode] that decides equal to itself, AND its own
    self-pointer tag [TPtr TListNode] (the [Next : *ListNode] field's type) round-trips too — both by
    [reflexivity], NO axiom.  Because the tag is nullary it never structurally contains itself, so
    there is no infinite [tag = TPtr tag] term; the recursion lives in the TYPE, the tag stays finite.
    These two facts are exactly what the typed heap needs to store/recover a [*ListNode] cell, so a
    multi-node linked list is allocatable + traversable (see [list_demo]). *)
Example tlistnode_tag_refl : tag_eq TListNode TListNode = Some eq_refl.
Proof. reflexivity. Qed.
Example tlistnode_selfptr_refl : tag_eq (TPtr TListNode) (TPtr TListNode) = Some eq_refl.
Proof. reflexivity. Qed.

(** "Channel that sends itself" tag soundness — the same crack through a CHANNEL.  [TChanBox] decides
    equal to itself, AND the channel-of-itself tag [TChan TChanBox] (the type [chan ChanBox] flowing
    through a [chan ChanBox]) round-trips — both by [reflexivity], NO axiom.  This is what the channel
    read-after-write at [chan ChanBox] needs, so a [ChanBox] containing its own channel is genuinely
    sendable + receivable (see [chanbox_demo]). *)
Example tchanbox_tag_refl : tag_eq TChanBox TChanBox = Some eq_refl.
Proof. reflexivity. Qed.
Example tchanbox_selfchan_refl : tag_eq (TChan TChanBox) (TChan TChanBox) = Some eq_refl.
Proof. reflexivity. Qed.

(** Every Go type has a zero value (false, 0, 0.0, nil, "", …) — its [GoTypeTag]
    determines which.  Now a DEFINITION (not an axiom): a recursion on the tag that
    is total precisely because [GoTypeTag] enumerates exactly the Go types and each
    has a concrete zero (the composite [GoChan]/[GoMap] zeros use the nil-location
    handle [MkChan 0]/[MkMap 0]; a slice's is [nil]).  The plugin lowers a
    [zero_val] CALL by name to the Go zero literal (0/false/""/nil), so this body
    affects only proofs, never the emitted Go.  (The default for a [recv] from an
    empty/closed channel, an out-of-range index, etc.) *)
Fixpoint zero_val {A : Type} (t : GoTypeTag A) {struct t} : A :=
  match t in GoTypeTag A' return A' with
  | TBool    => false
  | TInt64   => MkGoInt 0%Z (squash eq_refl)   (* platform-int zero — Z-carried record (mirrors TI64/TU64) *)
  | TFloat64 => S754_zero false
  | TString  => EmptyString
  | TU8  => MkU8 0%Z (squash eq_refl)  | TI8  => MkI8 0%Z (squash eq_refl)
  | TU16 => MkU16 0%Z (squash eq_refl) | TI16 => MkI16 0%Z (squash eq_refl)
  | TU32 => MkU32 0%Z (squash eq_refl) | TI32 => MkI32 0%Z (squash eq_refl)
  | TI64 => i64wrap 0%Z
  | TU64 => MkU64 0%Z (squash eq_refl)
  | TUnit => tt
  | TUint    => MkUint 0%Z (squash eq_refl)   (* platform-uint zero — [Z]-carried (mirrors [TU64]), faithful [0,2^64) *)
  | TFloat32 => f32_of_f64 (S754_zero false)    (* float32 zero, rounded in through the abstract type *)
  | TListNode => MkListNode (i64wrap 0%Z) (mkPtr 0)   (* zero recursive node: {0, nil} (plugin emits the Go struct zero; proof-only) *)
  | TChanBox => MkChanBox (i64wrap 0%Z) (MkChan 0)    (* zero box: {0, nil-chan} (proof-only) *)
  | TChan _  => MkChan 0       (* nil channel (handle erased; plugin emits nil) *)
  | TSlice _ => nil                   (* empty slice *)
  | TMap _ _ => MkMap 0        (* nil map *)
  | TArrow _ _ => NilFunc              (* func zero is the nil func ([NilFunc] : GoFunc _ _); plugin emits
                                          Go [nil].  FAITHFUL: NOT a callable codomain-zero
                                          placeholder — calling it (via [gofunc_call]) panics, like Go. *)
  | TProd a b => (zero_val a, zero_val b)  (* struct/pair zero: field-wise zeros *)
  | TPtr _   => mkPtr 0         (* nil pointer (handle erased; plugin emits nil) *)
  end.

(** ---- [GoAny] / [any] — Go's [interface{}] — a TAGGED (type, value) pair ----

    Go's [interface{}] carries its value's DYNAMIC TYPE at runtime, which is exactly
    what a type assertion [v.(T)] inspects.  So [GoAny] is a [{A & GoTypeTag A * A}]:
    the value [A] PLUS its runtime [GoTypeTag].  ([GoTypeTag] has no [TAny]
    constructor: [TAny : GoTypeTag GoAny] would be UNIVERSE-INCONSISTENT, the same
    wall as a tag-carrying [GoChan].  Sound because a value's dynamic type is always
    a CONCRETE type — Go flattens nested interfaces.  Lost: "assert TO [any]" /
    typed [chan any]/[[]any] containers; fail-loud, not an axiom.)

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
#[global] Instance Tagged_GoInt  : Tagged GoInt    := TInt64.   (* platform int — distinct Z-carried record *)
#[global] Instance Tagged_float  : Tagged GoFloat64 := TFloat64.
#[global] Instance Tagged_string : Tagged GoString := TString.
#[global] Instance Tagged_unit   : Tagged unit     := TUnit.
#[global] Instance Tagged_GoU8   : Tagged GoU8     := TU8.
#[global] Instance Tagged_GoI8   : Tagged GoI8     := TI8.
#[global] Instance Tagged_GoU16  : Tagged GoU16    := TU16.
#[global] Instance Tagged_GoI16  : Tagged GoI16    := TI16.
#[global] Instance Tagged_GoU32  : Tagged GoU32    := TU32.
#[global] Instance Tagged_GoI32  : Tagged GoI32    := TI32.
#[global] Instance Tagged_GoI64  : Tagged GoI64    := TI64.
#[global] Instance Tagged_GoU64  : Tagged GoU64    := TU64.
#[global] Instance Tagged_GoUint : Tagged GoUint   := TUint.   (* platform uint — distinct record ⇒ UNIQUE instance (one instance per Go type) *)
#[global] Instance Tagged_GoFloat32 : Tagged GoFloat32 := TFloat32.
#[global] Instance Tagged_ListNode : Tagged ListNode := TListNode.   (* recursive struct boxable / channel-payload *)
#[global] Instance Tagged_ChanBox  : Tagged ChanBox  := TChanBox.    (* "sends itself" struct boxable / channel-payload *)
#[global] Instance Tagged_prod {A B} `(Tagged A) `(Tagged B) : Tagged (A * B) :=
  TProd (the_tag A) (the_tag B).   (* a pair / 2-field struct backing infers its product tag *)
#[global] Instance Tagged_ptr {A} `(Tagged A) : Tagged (Ptr A) :=
  TPtr (the_tag A).                (* a [*T] handle infers its pointer tag — so it rides any/chan/map *)

