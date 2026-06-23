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
From Stdlib Require Import StrictProp.   (* Squash: carry a range invariant in SProp (proof-irrelevant ⇒ wrapper equality decided by the carrier alone, no axiom) *)
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
    [GoInt] models Go's [int].  Go's [int] is, BY SPEC, 32-OR-64-bit (implementation-specific,
    go.dev/ref/spec#Numeric_types), so NO deterministic model is faithful on every platform —
    this is an inherent property of [int], not a backend defect.  [GoInt := int] uses Rocq's
    primitive 63-bit machine integer ([PrimInt63]) with SIGNED (Sint63) semantics: [+]/[-]/[*]
    are two's-complement (so [2 - 5 = -3] as in Go, NOT the unsigned reading [2^63 - 3]);
    comparison and division use the signed Sint63 ops.  It renders to Go [int] (idiomatic — it
    matches [len]/[cap]/indexing, which are Go-[int]-typed; rendering as [int64] would force a
    cast at every such interop).  HONEST BOUNDED DEVIATION (a SUBSTRATE LIMIT — exactly the
    kind CLAUDE.md rule 2 permits): the 63-bit carrier is faithful to a 64-bit Go [int] only
    within [-2^62, 2^62) (and within [-2^31, 2^31) on a 32-bit Go).  An operation whose result
    reaches [±2^62] WRAPS in the model where 64-bit Go would not — but [2^62 ≈ 4.6e18] is far
    above any realistic index/length/size, so the divergence is UNREACHABLE in the index/size
    use case.  This is NOT enforced by a per-op range proof (that would be invasive for an
    unreachable case); for code that NEEDS the guaranteed full 64-bit range, use the FAITHFUL
    [GoI64]/[GoU64] records below (Z-carried, wrap EXACTLY at [2^64]). *)
(** Go's platform-width [int] — the 63-bit [Sint63] substrate (bounded deviation, see above).
    It IS Go's [int]: a transparent [int] alias is correct HERE, because the plugin ALSO renders
    [int] as Go [int] (no type-vs-rendering mismatch) and it boxes via [Tagged_int].

    The OTHER integer types are NOT transparent [int] aliases.  That was review #4 P0 #1: a
    transparent alias ([GoUint := int]) is freely cross-assignable in Rocq, yet the plugin renders
    it as a DISTINCT Go type ([uint]) — so [fun (x:GoInt) => (x:GoUint)] type-checks but extracts to
    the INVALID Go [func(x int) uint { return x }], and [any (x:GoUint)] mis-tags (only [Tagged_int]
    resolves, so it boxes as [int] not [uint]).  The fixed-width signed/unsigned family
    ([int8]…[uint64]) are the GENUINELY DISTINCT records [GoI8]/[GoU8]/…/[GoI64]/[GoU64] below, and
    Go's platform [uint] is the distinct record [GoUint] (defined by [GoU64]).  The dead bare-[int]
    placeholders [GoInt8]/[GoInt16]/[GoInt32]/[GoUint8]/…/[GoUint64] are RETIRED (one Rocq type per
    Go type); [GoRune] is now the faithful [GoI32] (bound after the records). *)
Definition GoInt : Type := int.   (* Go's platform-dependent int; 63-bit Sint63 substrate — bounded deviation, see above *)
(* [GoByte] (Go's [byte] = an alias for [uint8]) is bound after [GoU8] below, to
   the FAITHFUL [GoU8] record (NOT a bare-int placeholder). *)

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
    [GoFloat32] is an ABSTRACT binary32 wrapper over [float] (see below). *)
Require Import Coq.Numbers.Cyclic.Int63.PrimInt63.
From Stdlib Require Import Numbers.Cyclic.Int63.Sint63.
From Stdlib Require Import Floats.PrimFloat.
From Stdlib Require Import Floats.FloatOps Floats.SpecFloat.   (* [Prim2SF] — verified float decomposition for [int64(f)] truncation *)
(* [BinInt] gives [Z] for the FULL-WIDTH [GoI64] model below (the 63-bit primitive
   [int] is one bit short of int64).  Required WITHOUT [Open Scope Z_scope] so the
   existing [%uint63]/[%sint63] defaults are untouched — all [Z] use is qualified
   ([Z.add]/[Z.modulo]/…) with explicit [%Z] literals. *)
From Stdlib Require Import BinInt.
Notation GoFloat64 := float.

(** ---- float32 (binary32), SOUND abstract model ----

    Go's [float32] is IEEE binary32.  Rocq has no native 32-bit float, so a [GoFloat32]
    is carried by a binary64 [float] holding a binary32-REPRESENTABLE value.  The faithful
    binary32 rounding is [f32_round]: round to format (prec 24, emax 128) via SpecFloat's
    [SFmul …·1] — exactly Go's round-to-nearest-even at binary32.

    SOUNDNESS — closes a code-review hole.  Previously [GoFloat32 := float] (a transparent
    alias), so a NON-representable literal could be injected directly ([16777217%float :
    GoFloat32]) and widened with no rounding — making Rocq disagree with Go ([f64_of_f32]
    keeps [16777217] in Rocq, but Go's [float32] rounds it to [16777216]), which licenses
    UNSOUND proofs.  Now [GoFloat32] is an ABSTRACT record whose proof field [f32ok]
    witnesses that the carrier is in the IMAGE of [f32_round] — i.e. binary32-representable.
    [mkF32 16777217 _] is unconstructable: it would demand [exists a, 16777217 = f32_round a],
    which is false.  Every inhabitant enters through a rounding smart constructor ([f32_of_f64]
    / [f32_lit] / the arithmetic ops), so widening [f64_of_f32] (identity on the carrier) is
    SOUND — the carrier always equals its own binary32 value, matching Go's exact
    [float64(float32)].  ZERO new axioms: the provenance proofs are [eq_refl]; the trust base
    stays exactly Rocq's float primitives (machine-checked [Print Assumptions]).  At extraction
    [GoFloat32] erases to Go [float32] and [mkF32]/[f32val] to identity (the carrier IS the
    float32), so the emitted Go is unchanged. *)
Definition f32_round (v : float) : float :=
  SF2Prim (SFmul 24 128 (Prim2SF v) (Prim2SF 1%float)).
Record GoFloat32 : Type :=
  mkF32 { f32val : float ; f32ok : exists a : float, f32val = f32_round a }.
(** The only way IN: round a binary64 (or a literal) to binary32.  Provenance proof is
    [eq_refl] — the carrier is literally [f32_round a]. *)
Definition f32_of_f64 (a : GoFloat64) : GoFloat32 := mkF32 (f32_round a) (ex_intro _ a eq_refl).
(** A float32 LITERAL rounds at the Rocq boundary (Go rounds a typed constant the same way). *)
Definition f32_lit (a : GoFloat64) : GoFloat32 := f32_of_f64 a.

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
(** [Ptr A] is a phantom-LOCATION record too (TAG-FREE, like [GoChan]/[GoMap]) — the element type [A]
    is carried only in the type, never as a field.  This is what lets [GoTypeTag] reference it via
    [TPtr] (a tag-carrying [Ptr] would make [GoTypeTag] universe-inconsistent — same reason as the
    channel/map handles).  The pointee's type lives in the world heap cell ([RefCell] stores the tag),
    so the deref OPS ([ptr_get]/[ptr_set]/…) below take the [GoTypeTag] explicitly.  Extraction:
    [Ptr A] → Go [*T] (rendered by type name, like [chan T]); the [p_loc] handle is erased. *)
Record Ptr (A : Type) : Type := mkPtr { p_loc : int }.
Arguments mkPtr {A} _.
Arguments p_loc {A} _.

(** ---- Type assertions ----

    [GoTypeTag T] is a term-level witness encoding the Go type [T].
    Because it is an inductive (not a type), it survives extraction —
    the plugin inspects the constructor to emit [v.(T)] with the right type.

    Extend this inductive as new Go types are added to builtins. *)

(* [iN_norm] (8-bit shown) hoisted here so the signed wrapper records can carry a PROVENANCE
   invariant "the carrier is in the image of normalization" — i.e. it is a valid sign-extended
   N-bit value (parallel to GoFloat32's [f32_round] provenance).  Body uses only [PrimInt63]. *)
Definition i8_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 255) 128) 128.
Definition i16_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 65535) 32768) 32768.
Definition i32_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 4294967295) 2147483648) 2147483648.
(* int64/uint64 range predicates + wrap-to-range, hoisted so the GoI64/GoU64 records can carry a
   RANGE invariant.  Z-carried (not int63): int64 = [-2^63, 2^63), uint64 = [0, 2^64). *)
Definition in_i64 (z : Z) : bool :=
  andb (-9223372036854775808 <=? z)%Z (z <? 9223372036854775808)%Z.
Definition wrap64 (z : Z) : Z :=
  (Z.modulo (z + 9223372036854775808) 18446744073709551616 - 9223372036854775808)%Z.
Definition in_u64 (z : Z) : bool :=
  andb (0 <=? z)%Z (z <? 18446744073709551616)%Z.
Definition wrapU64 (z : Z) : Z :=
  Z.modulo z 18446744073709551616%Z.

(* Numeric-wrapper records, hoisted ABOVE GoTypeTag so TU8../TUnit can index them. *)
Record GoU8 := MkU8 { u8raw : int ; u8ok : Squash ((u8raw <? 256)%uint63 = true) }.
Record GoI8 := MkI8 { i8raw : int ; i8ok : Squash (exists a, i8raw = i8_norm a) }.
Record GoU16 := MkU16 { u16raw : int ; u16ok : Squash ((u16raw <? 65536)%uint63 = true) }.
Record GoI16 := MkI16 { i16raw : int ; i16ok : Squash (exists a, i16raw = i16_norm a) }.
Record GoU32 := MkU32 { u32raw : int ; u32ok : Squash ((u32raw <? 4294967296)%uint63 = true) }.
Record GoI32 := MkI32 { i32raw : int ; i32ok : Squash (exists a, i32raw = i32_norm a) }.
(* FULL-WIDTH signed int64 (Go spec "Numeric types": [int64] is the set of all
   signed 64-bit integers).  Carried by [Z] — NOT the 63-bit [int] — so the model
   is faithful across the WHOLE int64 range and wraps at the true [2^63], unlike
   the [Sint63] [int] carrier (faithful only within [-2^62, 2^62)).  The wrapper
   ERASES at extraction (like [GoU8]); a [GoI64] value is a Go [int64], which wraps
   natively at [2^64], so the emitted ops need no mask. *)
Record GoI64 := MkI64 { i64raw : Z ; i64ok : Squash (in_i64 i64raw = true) }.
(* FULL-WIDTH unsigned 64-bit integer (Go spec "Numeric types": [uint64] is the
   set of all unsigned 64-bit integers, range [0, 2^64)).  Carried by [Z] — NOT
   the 63-bit [int] — so the model is faithful across the whole uint64 range and
   wraps at [2^64].  The wrapper ERASES at extraction (like [GoI64]); a [GoU64]
   value is a Go [uint64], which wraps natively at [2^64], so the emitted ops
   need no mask. *)
Record GoU64 := MkU64 { u64raw : Z ; u64ok : Squash (in_u64 u64raw = true) }.

(* Go's platform-width UNSIGNED [uint] — a GENUINELY DISTINCT record (review #4 P0 #1), NOT a
   transparent [int] alias.  Carried by the 63-bit primitive [int] viewed UNSIGNED (uint63): the
   platform [int]/[uint] pair both ride the [Sint63]/[Uint63] substrate, exactly as the fixed-width
   [int64]/[uint64] pair both ride [Z] ([GoI64]/[GoU64]).  BOUNDED DEVIATION (a SUBSTRATE LIMIT, the
   kind CLAUDE.md rule 2 permits — IDENTICAL to [GoInt]'s): faithful to Go's [uint] within [0, 2^63);
   for the full 64-bit unsigned range use [GoU64].  [uintok] is a PHANTOM SProp field whose SOLE role
   is to defeat Coq's single-field-record unboxing — so the wrapper SURVIVES extraction as a distinct
   type (rendered [uint], its struct decl suppressed, ctor/proj erased) instead of collapsing to its
   [int] carrier.  There is no range to seal: EVERY 63-bit [int] is a valid platform-uint in the
   unsigned view (so [MkUint] is total, unlike the range-sealed [MkU8]).  Distinctness is what gives
   [Tagged_GoUint := TUint] a UNIQUE resolution ([Tagged_int] no longer applies, since [GoUint <> int]),
   closing the model/runtime tag inversion. *)
Record GoUint := MkUint { uintraw : int ; uintok : Squash True }.
(* The canonical platform-uint constructor — [uint_lit n] is Go's typed [uint(n)].  At extraction
   [MkUint]/[uint_lit] render [uint(<carrier>)] and [uintraw] renders [int(<value>)], so a [GoUint]
   value is valid Go in EVERY position (param/return/field/[any]-box): [any (uint_lit 5)] boxes as
   Go [uint], so [.(uint)] SUCCEEDS and [.(int)] FAILS — model and runtime agree. *)
Definition uint_lit (n : int) : GoUint := MkUint n (squash I).
(* Go's [rune] is an alias for [int32] — the FAITHFUL [GoI32] record (NOT the retired [GoInt32]
   placeholder), so a [rune] value (e.g. [i32wrap c]) is a real, distinct int32. *)
Notation GoRune := GoI32.

(* A genuinely RECURSIVE Go struct type — [type ListNode struct { Val int64 ; Next *ListNode }].
   Defined HERE (above [GoTypeTag]) precisely so the tag inductive can carry its NULLARY nominal tag
   [TListNode : GoTypeTag ListNode] below.  Two things make this work, axiom-free:
   (1) [Inductive] (NOT the [Record] keyword, which forbids self-reference) with record-projection
       syntax — extraction still classifies it as a record ⇒ the plugin emits a Go [struct].  The
       recursion is through [Ptr ListNode], and [Ptr] is a TAG-FREE phantom handle (pointee erased,
       stores no tag) ⇒ [ListNode] occurs vacuously-positively, so Rocq accepts it (and storing no
       tag keeps [GoTypeTag ListNode] universe-consistent — same reason [GoChan] is tag-free).
   (2) The supposed "cyclic type-tag wall" (a structural [tag = TPtr tag] would be an infinite term)
       is a MIRAGE: a NULLARY nominal tag does not structurally contain itself.  [TListNode] is a base
       case exactly like [TBool]; the [Next : *ListNode] field's tag is the FINITE term [TPtr TListNode].
       So the recursive TYPE gets a finite tag and round-trips through [tag_eq] (witnessed below). *)
Inductive ListNode := MkListNode { ln_val : GoI64 ; ln_next : Ptr ListNode }.

(* "CHANNELS THAT SEND THEMSELVES" — a struct holding a channel of its OWN type:
   [type ChanBox struct { Id int64 ; Ch chan ChanBox }].  A [chan ChanBox] can carry a [ChanBox]
   value whose [Ch] field IS that very channel, so the channel transmits something containing itself.
   Same crack as [ListNode] but the recursion goes through [GoChan] instead of [Ptr]: [GoChan] is a
   TAG-FREE phantom handle (element type erased, stores no tag) ⇒ [ChanBox] occurs vacuously-positively
   ([Inductive], not the recursion-forbidding [Record] keyword) AND [GoTypeTag ChanBox] stays universe-
   consistent.  Its nullary nominal tag [TChanBox] (below) is FINITE; the channel-of-itself tag is the
   finite term [TChan TChanBox].  2 fields ⇒ not unboxed ⇒ emits the named Go struct.  The channel
   read-after-write round-trip for it is ALREADY a theorem ([chan_buf_write_same], via [tag_eq_refl]). *)
Inductive ChanBox := MkChanBox { cb_id : GoI64 ; cb_chan : GoChan ChanBox }.

(* [i64wrap] = wrap-to-int64-range + carry the (SProp) range proof, so [i64wrap (2^63) _] is
   unconstructable.  Hoisted here (before the narrow→int64 conversions at [i64_of_u8]… use it). *)
Lemma in_i64_wrap64 : forall z, in_i64 (wrap64 z) = true.
Proof.
  intro z. unfold in_i64, wrap64.
  pose proof (Z.mod_pos_bound (z + 9223372036854775808) 18446744073709551616 ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition i64wrap (z : Z) : GoI64 := MkI64 (wrap64 z) (squash (in_i64_wrap64 z)).

Inductive GoTypeTag : Type -> Type :=
  | TBool    : GoTypeTag bool
  | TInt64   : GoTypeTag int             (* → int64 *)
  | TFloat64 : GoTypeTag float            (* → float64 *)
  | TString  : GoTypeTag GoString
  | TU8  : GoTypeTag GoU8  | TI8  : GoTypeTag GoI8
  | TU16 : GoTypeTag GoU16 | TI16 : GoTypeTag GoI16
  | TU32 : GoTypeTag GoU32 | TI32 : GoTypeTag GoI32
  | TI64 : GoTypeTag GoI64               (* → int64 (full-width Z-carried signed) *)
  | TU64 : GoTypeTag GoU64               (* → uint64 (full-width Z-carried unsigned) *)
  | TUnit : GoTypeTag unit
  (* Go's platform-width [int]/[uint] — distinct Go types, kept (e.g. [cap]/[len]
     return [GoInt]).  [TUint] now indexes the DISTINCT record [GoUint] (review #4 P0 #1):
     before, [GoUint := int], so this tag indexed [int] and clashed with [TInt64] (both Go
     [int] in the model yet [uint] vs [int] at runtime) — the tag inversion.  The FIXED-width
     bare-int aliases ([GoInt8]/…/[GoUint64]) had their own tags here too, but they DUPLICATEd
     the canonical Squash-sealed fixed-width family ([TI8]/[TU8]/…/[TI64]/[TU64]) — same Go type,
     two tags — break #7's soundness hole (a non-injective tag→runtime-Go-type makes [tag_eq]
     disagree with Go's [v.(T)]).  Those aliases are now RETIRED as TYPES entirely (review #4
     P0 #1), so one canonical tag AND one Rocq type per fixed-width Go type. *)
  (* [TInt64] IS Go's platform [int] now (break #7 slice 7c: PrimInt63 = Go int, the
     Z-carried [GoI64]/[TI64] is int64).  The old [TInt]:GoTypeTag GoInt was a SECOND tag
     for the same Go [int] (GoInt := int), with no [Tagged] instance and never boxed
     (GoInt values box via [Tagged_int]=[TInt64]) — a redundant tag, RETIRED here so [int]
     has exactly one tag. *)
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
  | TArrow : forall {A B : Type}, GoTypeTag A -> GoTypeTag B -> GoTypeTag (A -> B)
  (* product (pair) type — the SOUND backing for struct channels: unlike a nominal struct,
     [A * B] is CANONICAL, so [tag_eq] can recover [A1*B1 = A2*B2] from the component tags.
     A 2-field struct is modelled as a product (marshalled via its StructRep iso) yet still
     EXTRACTS to its native named Go struct — methods/embedding intact. *)
  | TProd : forall {A B : Type}, GoTypeTag A -> GoTypeTag B -> GoTypeTag (A * B)
  (* pointer type [*T] — a tag-free [Ptr A] handle (defined above, like [GoChan]); the element tag is
     recovered by [tag_eq] so a [*T] can be a channel payload / [any] box / map value.  [==] on
     pointers compares the location (Go compares addresses). *)
  | TPtr : forall {A : Type}, GoTypeTag A -> GoTypeTag (Ptr A).

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
Definition goarrow_cong {A A' B B'} (p : A = A') (q : B = B')
  : @eq Type (A -> B) (A' -> B') :=
  match p in (_ = A2), q in (_ = B2) return (@eq Type (A -> B) (A2 -> B2)) with
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
      | Some p, Some q => Some (goarrow_cong p q)
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
  - rewrite IHt1, IHt2; reflexivity.                (* TArrow (goarrow_cong reduces) *)
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
  | TInt64   => 0%uint63
  | TFloat64 => 0%float
  | TString  => EmptyString
  | TU8  => MkU8 0%uint63 (squash eq_refl)  | TI8  => MkI8 0%uint63 (squash (ex_intro _ 0%uint63 eq_refl))
  | TU16 => MkU16 0%uint63 (squash eq_refl) | TI16 => MkI16 0%uint63 (squash (ex_intro _ 0%uint63 eq_refl))
  | TU32 => MkU32 0%uint63 (squash eq_refl) | TI32 => MkI32 0%uint63 (squash (ex_intro _ 0%uint63 eq_refl))
  | TI64 => i64wrap 0%Z
  | TU64 => MkU64 0%Z (squash eq_refl)
  | TUnit => tt
  | TUint    => uint_lit 0%uint63
  | TFloat32 => f32_of_f64 0%float    (* float32 zero, rounded in through the abstract type *)
  | TListNode => MkListNode (i64wrap 0%Z) (mkPtr 0%uint63)   (* zero recursive node: {0, nil} (plugin emits the Go struct zero; proof-only) *)
  | TChanBox => MkChanBox (i64wrap 0%Z) (MkChan 0%uint63)    (* zero box: {0, nil-chan} (proof-only) *)
  | TChan _  => MkChan 0%uint63       (* nil channel (handle erased; plugin emits nil) *)
  | TSlice _ => nil                   (* empty slice *)
  | TMap _ _ => MkMap 0%uint63        (* nil map *)
  | TArrow _ b => fun _ => zero_val b  (* func zero: plugin emits Go [nil]; this returning-codomain-
                                          zero inhabitant is a proof-only placeholder (a real nil func
                                          panics if called, but zero_val is a never-called default) *)
  | TProd a b => (zero_val a, zero_val b)  (* struct/pair zero: field-wise zeros *)
  | TPtr _   => mkPtr 0%uint63         (* nil pointer (handle erased; plugin emits nil) *)
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
#[global] Instance Tagged_GoU64  : Tagged GoU64    := TU64.
#[global] Instance Tagged_GoUint : Tagged GoUint   := TUint.   (* platform uint — distinct record ⇒ UNIQUE instance (Tagged_int no longer applies); review #4 P0 #1 *)
#[global] Instance Tagged_GoFloat32 : Tagged GoFloat32 := TFloat32.
#[global] Instance Tagged_ListNode : Tagged ListNode := TListNode.   (* recursive struct boxable / channel-payload *)
#[global] Instance Tagged_ChanBox  : Tagged ChanBox  := TChanBox.    (* "sends itself" struct boxable / channel-payload *)
#[global] Instance Tagged_prod {A B} `(Tagged A) `(Tagged B) : Tagged (A * B) :=
  TProd (the_tag A) (the_tag B).   (* a pair / 2-field struct backing infers its product tag *)
#[global] Instance Tagged_ptr {A} `(Tagged A) : Tagged (Ptr A) :=
  TPtr (the_tag A).                (* a [*T] handle infers its pointer tag — so it rides any/chan/map *)

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
Fixpoint key_eqb {K} (t : GoTypeTag K) {struct t} : K -> K -> bool :=
  match t in GoTypeTag K' return K' -> K' -> bool with
  | TBool    => Bool.eqb
  | TInt64   => PrimInt63.eqb | TUint   => fun a b => PrimInt63.eqb (uintraw a) (uintraw b)
  | TString  => String.eqb
  | TFloat64 => PrimFloat.eqb | TFloat32 => fun a b => PrimFloat.eqb (f32val a) (f32val b)
  | TU8  => fun a b => PrimInt63.eqb (u8raw a) (u8raw b)
  | TI8  => fun a b => PrimInt63.eqb (i8raw a) (i8raw b)
  | TU16 => fun a b => PrimInt63.eqb (u16raw a) (u16raw b)
  | TI16 => fun a b => PrimInt63.eqb (i16raw a) (i16raw b)
  | TU32 => fun a b => PrimInt63.eqb (u32raw a) (u32raw b)
  | TI32 => fun a b => PrimInt63.eqb (i32raw a) (i32raw b)
  | TI64 => fun a b => Z.eqb (i64raw a) (i64raw b)
  | TU64 => fun a b => Z.eqb (u64raw a) (u64raw b)
  | TUnit => fun _ _ => true
  | TChan _  => fun a b => PrimInt63.eqb (ch_loc a) (ch_loc b)
  | TSlice _ => fun _ _ => false
  | TMap _ _ => fun a b => PrimInt63.eqb (gm_loc a) (gm_loc b)
  | TArrow _ _ => fun _ _ => false   (* func types are NOT comparable in Go (sentinel, like slices) *)
  | TProd a b => fun x y => andb (key_eqb a (fst x) (fst y)) (key_eqb b (snd x) (snd y))
                                     (* a product (comparable struct) is a valid key iff both fields are *)
  | TPtr _ => fun a b => PrimInt63.eqb (p_loc a) (p_loc b)   (* Go [==] on pointers compares addresses *)
  | TListNode => fun a b => andb (Z.eqb (i64raw (ln_val a)) (i64raw (ln_val b)))
                                 (PrimInt63.eqb (p_loc (ln_next a)) (p_loc (ln_next b)))
                                     (* a [ListNode] IS comparable in Go (all fields are: int64 + a pointer):
                                        field-wise == — equal [Val] AND same [Next] address. NOT a [false] sentinel. *)
  | TChanBox => fun a b => andb (Z.eqb (i64raw (cb_id a)) (i64raw (cb_id b)))
                                (PrimInt63.eqb (ch_loc (cb_chan a)) (ch_loc (cb_chan b)))
                                     (* a [ChanBox] IS comparable in Go (int64 + a channel; channels compare by
                                        identity): field-wise == — equal [Id] AND same [Ch] channel. *)
  end.

(** [Comparable t]: [key_eqb t] decides equality on [K] — the typing side
    condition Go imposes on map keys, made explicit. *)
Definition Comparable {K} (t : GoTypeTag K) : Prop :=
  forall a b : K, key_eqb t a b = true <-> a = b.

(** The scalar key types ARE comparable (used by every map demo: int keys). *)
Lemma comparable_TInt64 : Comparable TInt64.
Proof. intros a b. cbn. apply Uint63.eqb_spec. Qed.

(** The full-width [GoI64]/[GoU64] are comparable too (A4.2b): [key_eqb] decides
    equality via [Z.eqb] on the carrier, so they are first-class MAP KEY types —
    [int64]/[uint64] keys, exactly like Go.  (Single-field record: equality of the
    [Z] carrier is equality of the value.) *)
Lemma comparable_TI64 : Comparable TI64.
Proof.
  intros [za] [zb]. cbn. split.
  - intro H. apply Z.eqb_eq in H. subst. reflexivity.
  - intro H. injection H as ->. apply Z.eqb_refl.
Qed.
Lemma comparable_TU64 : Comparable TU64.
Proof.
  intros [za] [zb]. cbn. split.
  - intro H. apply Z.eqb_eq in H. subst. reflexivity.
  - intro H. injection H as ->. apply Z.eqb_refl.
Qed.

(** ---- Break #7: the tag → runtime-Go-type map is INJECTIVE (the anti-regression LOCK) ----

    A type assertion [v.(T)] in the EMITTED Go targets the Go type the plugin prints for the
    tag [T] (its [go_type_tag_map] entry).  [go_runtime_name] MIRRORS that map for the SCALAR
    tags — each has a faithful, DISTINCT Go type.  The soundness a type assertion needs: the
    model's [tag_eq] must not distinguish what Go cannot — two tags the model calls different
    ([tag_eq = None]) MUST lower to DIFFERENT Go types, else [v.(Tb)] would succeed on a
    [Ta]-boxed value exactly where the model's assertion fails.  [tag_runtime_agrees] proves
    that over the named tags.  It is UNPROVABLE if any two named tags share a Go name — so it
    is a machine-checked LOCK against re-introducing break #7's collisions, all now closed:
    [TInt64]/[TI64] (int vs int64, slice 7c), the narrow cluster (uint8…int32, 7b),
    [TUint64]/[TU64] and the dead bare-width tags (7a).

    Scope: the [None] tags ([TUnit], [TArrow], the composites) are out of scope — a composite's
    injectivity REDUCES to this one (it recurses on element tags, e.g. [chan T1] = [chan T2] iff
    [T1]=[T2]), and unit/func assert to Go [any] (the documented [GoAny] "no assert-to-interface"
    limit, not a collision). *)
Definition go_runtime_name {A} (t : GoTypeTag A) : option string :=
  (match t with
   | TBool    => Some "bool"
   | TInt64   => Some "int"        (* PrimInt63 = Go's platform int (7c) *)
   | TFloat64 => Some "float64"
   | TString  => Some "string"
   | TUint    => Some "uint"
   | TU8  => Some "uint8"  | TI8  => Some "int8"
   | TU16 => Some "uint16" | TI16 => Some "int16"
   | TU32 => Some "uint32" | TI32 => Some "int32"
   | TI64 => Some "int64"          (* Z-carried GoI64 — DISTINCT from [TInt64] = int *)
   | TU64 => Some "uint64"
   | TFloat32 => Some "float32"
   | _ => None
   end)%string.

Theorem tag_runtime_agrees :
  forall {A B} (ta : GoTypeTag A) (tb : GoTypeTag B) (sa sb : string),
    go_runtime_name ta = Some sa ->
    go_runtime_name tb = Some sb ->
    tag_eq ta tb = None ->
    sa <> sb.
Proof.
  intros A B ta tb sa sb Ha Hb Hne.
  destruct ta, tb; cbn in *; congruence.
Qed.
(* Zero-assumption by construction: the proof is pure [destruct]/[cbn]/[congruence] over the
   [tag_eq] and [go_runtime_name] Definitions — every step a primitive tactic over total
   Definitions, with no opaque holes, never appealing to the PrimInt63/PrimFloat primitives
   or the [funext] holdout. *)

(** The 7c payoff for the spec's "all numeric types are distinct" (Numeric types): the
    platform [int] ([TInt64], PrimInt63) and [int64] ([TI64], the Z-carried [GoI64]) now
    lower to DIFFERENT Go types, so Go's runtime type identity ([v.(int)] vs [v.(int64)])
    distinguishes them — it did NOT before 7c, when BOTH lowered to Go [int64] (a hidden
    distinctness violation).  A direct instance of [tag_runtime_agrees]. *)
Example int_vs_int64_distinct : go_runtime_name TInt64 <> go_runtime_name TI64.
Proof. cbn. discriminate. Qed.

(** Native struct equality — Go's [a == b] on a comparable struct (spec "Comparison
    operators": struct values are comparable iff all fields are, and [==] is field-wise).
    EVIDENCE-CARRYING and safe-by-construction: it DEMANDS not just a candidate [eqb] but a
    SEALED PROOF [pf] that [eqb] DECIDES equality ([forall x y, eqb x y = true <-> x = y]) —
    the comparability witness Go requires before you may write [==] — and only then lowers to
    the bare native [a == b] (the witness having discharged the comparability side condition,
    exactly as [div_nz] discharges the non-zero-divisor guard).  Because [pf] is in [SProp] it
    is ERASED at extraction, so [struct_eqb eqb pf a b] extracts to the same 3-arg shape the
    plugin lowers to [a == b] — the seal costs nothing at runtime but makes the bogus witness
    [struct_eqb (fun _ _ => false) ? a b] UNCONSTRUCTABLE (its [pf] obligation is unprovable).
    [struct_eqb eqb pf a b] is definitionally [eqb a b], so since [eqb] decides equality so
    does [==] (e.g. [struct_eqb_native_spec]). *)
Definition struct_eqb {R : Type} (eqb : R -> R -> bool)
                      (pf : Squash (forall x y, eqb x y = true <-> x = y))
                      (a b : R) : bool := eqb a b.

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
(** The leading [int] is the map's SIZE (number of live keys) — so Go's [len(m)] is faithfully modelled
    ([map_size]), maintained by [map_upd] (+1 on a genuinely new key) and [map_rem] (−1 on a present key).
    It sits OUTSIDE the existT (size is type-independent), so the value accessor [map_get_fn] is unchanged. *)
Definition MapCell : Type :=
  (int * { K : Type & (GoTypeTag K * { V : Type & (GoTypeTag V * (K -> option V))%type })%type })%type.
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
(** The mask [land x 255] is always [< 256] (zeroes bits ≥ 8) — the range invariant every [uint8] op
    preserves.  Proved via the [land = mod 2^8] law.  [u8wrap] is the ONLY internal constructor of a
    computed [GoU8]: it MASKS and carries the (SProp-erased) proof, so the forged [MkU8 300 _] is
    UNCONSTRUCTABLE ([300 < 256] is false).  SProp ⇒ proof irrelevance ⇒ two [GoU8] with equal
    [u8raw] are definitionally equal (so value witnesses ignore the proof). *)
Lemma land255_lt256 : forall x, (PrimInt63.land x 255 <? 256)%uint63 = true.
Proof.
  intro x. apply Uint63.ltb_spec. rewrite Uint63.land_spec'.
  pose proof (Uint63.to_Z_bounded x) as Hb.
  change (Uint63.to_Z 255) with 255%Z. change (Uint63.to_Z 256) with 256%Z.
  replace 255%Z with (Z.ones 8) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Definition u8wrap (x : int) : GoU8 := MkU8 (PrimInt63.land x 255) (squash (land255_lt256 x)).
Definition u8_lit (x : int) (pf : (x <? 256)%uint63 = true) : GoU8 := MkU8 x (squash pf).
Definition u8_add (a b : GoU8) : GoU8 := u8wrap (PrimInt63.land (PrimInt63.add (u8raw a) (u8raw b)) 255).
Definition u8_sub (a b : GoU8) : GoU8 := u8wrap (PrimInt63.land (PrimInt63.sub (u8raw a) (u8raw b)) 255).
Definition u8_mul (a b : GoU8) : GoU8 := u8wrap (PrimInt63.land (PrimInt63.mul (u8raw a) (u8raw b)) 255).
Definition u8_eqb (a b : GoU8) : bool := PrimInt63.eqb (u8raw a) (u8raw b).  (* in-range ⇒ exact *)
Definition u8_ltb (a b : GoU8) : bool := PrimInt63.ltb (u8raw a) (u8raw b).  (* in-range ⇒ unsigned = signed *)
Definition u8_leb (a b : GoU8) : bool := PrimInt63.leb (u8raw a) (u8raw b).

(* Build-checked: [uint8] and [int] do NOT mix — no implicit conversion. *)
Fail Definition u8_no_implicit (x : GoU8) : GoU8 := u8_add x (5 : int).
(* Build-checked: an out-of-range constant is UNREPRESENTABLE (Go: "overflows uint8"). *)
Fail Definition u8_const_oob : GoU8 := u8_lit 300 eq_refl.
(* Build-checked: even the RAW constructor cannot forge an out-of-range uint8 — [MkU8] now demands a
   proof [u8raw < 256] (code-review fix: was [MkU8 300], erased to the impossible value 300). *)
Fail Definition u8_forged : GoU8 := MkU8 300 (squash eq_refl).

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
(* [i8_norm] is hoisted up to the wrapper-record block (the GoI8 provenance invariant needs it).
   [i8wrap] is the internal constructor: normalize to 8-bit signed + carry the (trivial) provenance
   proof, so a forged [MkI8 200 _] is unconstructable (200 is not in [i8_norm]'s image). *)
Definition i8wrap (x : int) : GoI8 := MkI8 (i8_norm x) (squash (ex_intro _ x eq_refl)).
Definition i8_lit (x : int) (_ : (Sint63.leb (-128)%sint63 x && Sint63.ltb x 128)%bool = true) : GoI8 := i8wrap x.
Definition i8_add (a b : GoI8) : GoI8 := i8wrap (PrimInt63.add (i8raw a) (i8raw b)).
Definition i8_sub (a b : GoI8) : GoI8 := i8wrap (PrimInt63.sub (i8raw a) (i8raw b)).
Definition i8_mul (a b : GoI8) : GoI8 := i8wrap (PrimInt63.mul (i8raw a) (i8raw b)).
Definition i8_eqb (a b : GoI8) : bool := PrimInt63.eqb (i8raw a) (i8raw b).
Definition i8_ltb (a b : GoI8) : bool := Sint63.ltb (i8raw a) (i8raw b).   (* SIGNED comparison *)
Definition i8_leb (a b : GoI8) : bool := Sint63.leb (i8raw a) (i8raw b).

(** Direct [>] / [>=] / [!=] for the fixed-width types, completing Go's six comparison
    operators (here for [uint8]/[int8] — representative; the plugin's [fw_is] recognizes
    the same op on EVERY width, so [u16]/[i16]/[u32]/[i32] are identical one-liners).
    Defined as the swapped [</<=] and [negb (==)] but recognized by name and lowered to
    the DIRECT Go operator. *)
Definition u8_gtb  (a b : GoU8) : bool := u8_ltb b a.
Definition u8_geb  (a b : GoU8) : bool := u8_leb b a.
Definition u8_neqb (a b : GoU8) : bool := negb (u8_eqb a b).
Definition i8_gtb  (a b : GoI8) : bool := i8_ltb b a.
Definition i8_geb  (a b : GoI8) : bool := i8_leb b a.
Definition i8_neqb (a b : GoI8) : bool := negb (i8_eqb a b).

(** [uint16] / [int16] — the same template at width 16 (mask [0xffff]; sign bit
    [0x8000]).  Still fully faithful on the 63-bit carrier: a 16-bit product is
    [< 2^32], far below the [2^62] boundary, so [mul] is exact too. *)
(** [land x 65535] is always [< 65536] — the [uint16] range invariant (parallel to [land255_lt256]).
    [u16wrap] masks + carries the SProp proof, so a forged [MkU16 70000 _] is unconstructable. *)
Lemma land65535_lt65536 : forall x, (PrimInt63.land x 65535 <? 65536)%uint63 = true.
Proof.
  intro x. apply Uint63.ltb_spec. rewrite Uint63.land_spec'.
  pose proof (Uint63.to_Z_bounded x) as Hb.
  change (Uint63.to_Z 65535) with 65535%Z. change (Uint63.to_Z 65536) with 65536%Z.
  replace 65535%Z with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Definition u16wrap (x : int) : GoU16 := MkU16 (PrimInt63.land x 65535) (squash (land65535_lt65536 x)).
Definition u16_lit (x : int) (pf : (x <? 65536)%uint63 = true) : GoU16 := MkU16 x (squash pf).
Definition u16_add (a b : GoU16) : GoU16 := u16wrap (PrimInt63.land (PrimInt63.add (u16raw a) (u16raw b)) 65535).
Definition u16_sub (a b : GoU16) : GoU16 := u16wrap (PrimInt63.land (PrimInt63.sub (u16raw a) (u16raw b)) 65535).
Definition u16_mul (a b : GoU16) : GoU16 := u16wrap (PrimInt63.land (PrimInt63.mul (u16raw a) (u16raw b)) 65535).
Definition u16_eqb (a b : GoU16) : bool := PrimInt63.eqb (u16raw a) (u16raw b).
Definition u16_ltb (a b : GoU16) : bool := PrimInt63.ltb (u16raw a) (u16raw b).
Definition u16_leb (a b : GoU16) : bool := PrimInt63.leb (u16raw a) (u16raw b).

(* [i16_norm] hoisted to the wrapper-record block (the GoI16 provenance invariant needs it).
   [i16wrap] = normalize + carry the trivial provenance proof, so [MkI16 40000 _] is unconstructable. *)
Definition i16wrap (x : int) : GoI16 := MkI16 (i16_norm x) (squash (ex_intro _ x eq_refl)).
Definition i16_lit (x : int) (_ : (Sint63.leb (-32768)%sint63 x && Sint63.ltb x 32768)%bool = true) : GoI16 := i16wrap x.
Definition i16_add (a b : GoI16) : GoI16 := i16wrap (PrimInt63.add (i16raw a) (i16raw b)).
Definition i16_sub (a b : GoI16) : GoI16 := i16wrap (PrimInt63.sub (i16raw a) (i16raw b)).
Definition i16_mul (a b : GoI16) : GoI16 := i16wrap (PrimInt63.mul (i16raw a) (i16raw b)).
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
(* Build-checked: the RAW constructor cannot forge an out-of-range int8 — the provenance proof
   [exists a, 200 = i8_norm a] is false (200 is not a normalized 8-bit signed value). *)
Fail Definition i8_forged : GoI8 := MkI8 200 (squash (ex_intro _ 200 eq_refl)).
Fail Definition u16_const_oob : GoU16 := u16_lit 70000  eq_refl.   (* >= 2^16 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint16 (SProp range proof). *)
Fail Definition u16_forged : GoU16 := MkU16 70000 (squash eq_refl).
Fail Definition i16_const_oob : GoI16 := i16_lit 40000  eq_refl.   (* > 32767 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int16 (provenance proof false). *)
Fail Definition i16_forged : GoI16 := MkI16 40000 (squash (ex_intro _ 40000 eq_refl)).

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
Definition u8_and     (a b : GoU8)  : GoU8  := u8wrap (PrimInt63.land (u8raw a) (u8raw b)).
Definition u8_or      (a b : GoU8)  : GoU8  := u8wrap (PrimInt63.lor  (u8raw a) (u8raw b)).
Definition u8_xor     (a b : GoU8)  : GoU8  := u8wrap (PrimInt63.lxor (u8raw a) (u8raw b)).
Definition u8_andnot  (a b : GoU8)  : GoU8  := u8wrap (PrimInt63.land (u8raw a) (PrimInt63.lxor (u8raw b) 255)).
Definition u8_not     (a   : GoU8)  : GoU8  := u8wrap (PrimInt63.lxor (u8raw a) 255).
Definition i8_and     (a b : GoI8)  : GoI8  := i8wrap (i8_norm (PrimInt63.land (i8raw a) (i8raw b))).
Definition i8_or      (a b : GoI8)  : GoI8  := i8wrap (i8_norm (PrimInt63.lor  (i8raw a) (i8raw b))).
Definition i8_xor     (a b : GoI8)  : GoI8  := i8wrap (i8_norm (PrimInt63.lxor (i8raw a) (i8raw b))).
Definition i8_andnot  (a b : GoI8)  : GoI8  := i8wrap (i8_norm (PrimInt63.land (i8raw a) (PrimInt63.lxor (i8raw b) 255))).
Definition i8_not     (a   : GoI8)  : GoI8  := i8wrap (i8_norm (PrimInt63.lxor (i8raw a) 255)).
Definition u16_and    (a b : GoU16) : GoU16 := u16wrap (PrimInt63.land (u16raw a) (u16raw b)).
Definition u16_or     (a b : GoU16) : GoU16 := u16wrap (PrimInt63.lor  (u16raw a) (u16raw b)).
Definition u16_xor    (a b : GoU16) : GoU16 := u16wrap (PrimInt63.lxor (u16raw a) (u16raw b)).
Definition u16_andnot (a b : GoU16) : GoU16 := u16wrap (PrimInt63.land (u16raw a) (PrimInt63.lxor (u16raw b) 65535)).
Definition u16_not    (a   : GoU16) : GoU16 := u16wrap (PrimInt63.lxor (u16raw a) 65535).
Definition i16_and    (a b : GoI16) : GoI16 := i16wrap (i16_norm (PrimInt63.land (i16raw a) (i16raw b))).
Definition i16_or     (a b : GoI16) : GoI16 := i16wrap (i16_norm (PrimInt63.lor  (i16raw a) (i16raw b))).
Definition i16_xor    (a b : GoI16) : GoI16 := i16wrap (i16_norm (PrimInt63.lxor (i16raw a) (i16raw b))).
Definition i16_andnot (a b : GoI16) : GoI16 := i16wrap (i16_norm (PrimInt63.land (i16raw a) (PrimInt63.lxor (i16raw b) 65535))).
Definition i16_not    (a   : GoI16) : GoI16 := i16wrap (i16_norm (PrimInt63.lxor (i16raw a) 65535)).

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
Definition u8_shl  (x : GoU8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoU8  := u8wrap (PrimInt63.land (PrimInt63.lsl (u8raw x) k) 255).
Definition u8_shr  (x : GoU8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoU8  := u8wrap (PrimInt63.lsr (u8raw x) k).
Definition i8_shl  (x : GoI8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoI8  := i8wrap (i8_norm (PrimInt63.lsl (i8raw x) k)).
Definition i8_shr  (x : GoI8)  (k : int) (_ : (Sint63.leb 0 k) = true) : GoI8  := i8wrap (i8_norm (PrimInt63.asr (i8raw x) k)).
Definition u16_shl (x : GoU16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU16 := u16wrap (PrimInt63.land (PrimInt63.lsl (u16raw x) k) 65535).
Definition u16_shr (x : GoU16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU16 := u16wrap (PrimInt63.lsr (u16raw x) k).
Definition i16_shl (x : GoI16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI16 := i16wrap (i16_norm (PrimInt63.lsl (i16raw x) k)).
Definition i16_shr (x : GoI16) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI16 := i16wrap (i16_norm (PrimInt63.asr (i16raw x) k)).

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
Definition u8_of_int  (x : int) : GoU8  := u8wrap (PrimInt63.land x 255).
Definition i8_of_int  (x : int) : GoI8  := i8wrap (i8_norm x).
Definition u16_of_int (x : int) : GoU16 := u16wrap (PrimInt63.land x 65535).
Definition i16_of_int (x : int) : GoI16 := i16wrap (i16_norm x).

(* Build-checked: a conversion takes an [int], NOT another fixed-width type — so a
   cross-type conversion MUST go through [int] (e.g. [u8_of_int (int_of_i16 y)]),
   never [u8_of_int y] directly. *)
Fail Definition u8_of_i16_direct (y : GoI16) : GoU8 := u8_of_int y.

(** ---- Narrow -> full-width int64 WIDENING (Go [int64(x)]) ----
    Widen a fixed-width [uintN]/[intN] to the CANONICAL [int64] ([GoI64]).  The
    value is PRESERVED: an unsigned narrow ([0..2^N-1]) and a signed narrow
    ([-2^(N-1)..2^(N-1)-1]) both fit int64 exactly, so [Sint63.to_Z] of the carrier
    (the value's SIGNED [Z] reading — correct for both, since the unsigned narrows
    are [< 2^32 < 2^62] and the signed narrows hold their sign-extended value) is in
    range and lands unchanged in [GoI64].  Distinct from the narrow [int_of_FW]
    (which targets the index-[int]); these target the value-[int64].
    MODELED + machine-checked (witnesses in main.v).  *Runtime lowering DEFERRED,
    proof-only for now (no demo, not reachable from [main_effect] so not extracted):*
    the lowering WOULD be identity (the narrow already erases to a Go [int64] holding
    exactly this value, so [int64(x)] is a no-op cast), but the faithful body crosses
    the PrimInt63 -> Z carrier via [Sint63.to_Z], whose stdlib chain
    ([Sint63Axioms.to_Z] -> the DELIBERATELY-REJECTED unsigned [Uint63.ltb], Tier 3 #9)
    fights clean extraction-suppression.  A runtime form needs an int63 -> Z that drags
    no match-bodied stdlib decls.  Mirrors [f64_of_i64] (modeled, lowering deferred). *)
Definition i64_of_u8  (a : GoU8)  : GoI64 := i64wrap (Sint63.to_Z (u8raw  a)).
Definition i64_of_i8  (a : GoI8)  : GoI64 := i64wrap (Sint63.to_Z (i8raw  a)).
Definition i64_of_u16 (a : GoU16) : GoI64 := i64wrap (Sint63.to_Z (u16raw a)).
Definition i64_of_i16 (a : GoI16) : GoI64 := i64wrap (Sint63.to_Z (i16raw a)).
Definition i64_of_u32 (a : GoU32) : GoI64 := i64wrap (Sint63.to_Z (u32raw a)).
Definition i64_of_i32 (a : GoI32) : GoI64 := i64wrap (Sint63.to_Z (i32raw a)).

(** ---- Fixed-width division / remainder (Go spec "Arithmetic operators": [/ %]) ----
    EVIDENCE-CARRYING like [div_nz]: demand the divisor be non-zero (Go panics on a
    zero divisor), so the panic is unreachable (safe-by-construction).
    - [uintN]: the carrier is non-negative, so the SIGNED primitives [divs]/[mods]
      compute the UNSIGNED quotient/remainder; the result is in range (quotient
      <= dividend, |remainder| < divisor), no mask.
    - [intN]: SIGNED div/mod (truncate toward zero), wrapped to the width ([norm]) —
      this is where the most-negative / [-1] overflow lands: Go [int8(-128)/int8(-1)
      = -128] (two's-complement wrap), and [norm] gives exactly that. *)
Definition u8_div  (a b : GoU8)  (_ : (PrimInt63.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (PrimInt63.divs (u8raw a) (u8raw b)).
Definition u8_mod  (a b : GoU8)  (_ : (PrimInt63.eqb (u8raw b)  0) = false) : GoU8  := u8wrap (PrimInt63.mods (u8raw a) (u8raw b)).
Definition i8_div  (a b : GoI8)  (_ : (PrimInt63.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (i8_norm (PrimInt63.divs (i8raw a) (i8raw b))).
Definition i8_mod  (a b : GoI8)  (_ : (PrimInt63.eqb (i8raw b)  0) = false) : GoI8  := i8wrap (i8_norm (PrimInt63.mods (i8raw a) (i8raw b))).
Definition u16_div (a b : GoU16) (_ : (PrimInt63.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (PrimInt63.divs (u16raw a) (u16raw b)).
Definition u16_mod (a b : GoU16) (_ : (PrimInt63.eqb (u16raw b) 0) = false) : GoU16 := u16wrap (PrimInt63.mods (u16raw a) (u16raw b)).
Definition i16_div (a b : GoI16) (_ : (PrimInt63.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (i16_norm (PrimInt63.divs (i16raw a) (i16raw b))).
Definition i16_mod (a b : GoI16) (_ : (PrimInt63.eqb (i16raw b) 0) = false) : GoI16 := i16wrap (i16_norm (PrimInt63.mods (i16raw a) (i16raw b))).

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
(** [land x (2^32-1)] is always [< 2^32] — the [uint32] range invariant (parallel to
    [land255_lt256]).  [u32wrap] masks + carries the SProp proof; forged [MkU32 5000000000 _] is
    unconstructable. *)
Lemma land32_lt : forall x, (PrimInt63.land x 4294967295 <? 4294967296)%uint63 = true.
Proof.
  intro x. apply Uint63.ltb_spec. rewrite Uint63.land_spec'.
  pose proof (Uint63.to_Z_bounded x) as Hb.
  change (Uint63.to_Z 4294967295) with 4294967295%Z. change (Uint63.to_Z 4294967296) with 4294967296%Z.
  replace 4294967295%Z with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Definition u32wrap (x : int) : GoU32 := MkU32 (PrimInt63.land x 4294967295) (squash (land32_lt x)).
Definition u32_lit (x : int) (pf : (x <? 4294967296)%uint63 = true) : GoU32 := MkU32 x (squash pf).
Definition u32_add (a b : GoU32) : GoU32 := u32wrap (PrimInt63.land (PrimInt63.add (u32raw a) (u32raw b)) 4294967295).
Definition u32_sub (a b : GoU32) : GoU32 := u32wrap (PrimInt63.land (PrimInt63.sub (u32raw a) (u32raw b)) 4294967295).
Definition u32_mul (a b : GoU32) : GoU32 := u32wrap (PrimInt63.land (PrimInt63.mul (u32raw a) (u32raw b)) 4294967295).  (* low 32 bits exact: 2^32 | 2^63 *)
Definition u32_eqb (a b : GoU32) : bool := PrimInt63.eqb (u32raw a) (u32raw b).
Definition u32_ltb (a b : GoU32) : bool := PrimInt63.ltb (u32raw a) (u32raw b).
Definition u32_leb (a b : GoU32) : bool := PrimInt63.leb (u32raw a) (u32raw b).
Definition u32_and    (a b : GoU32) : GoU32 := u32wrap (PrimInt63.land (u32raw a) (u32raw b)).
Definition u32_or     (a b : GoU32) : GoU32 := u32wrap (PrimInt63.lor  (u32raw a) (u32raw b)).
Definition u32_xor    (a b : GoU32) : GoU32 := u32wrap (PrimInt63.lxor (u32raw a) (u32raw b)).
Definition u32_andnot (a b : GoU32) : GoU32 := u32wrap (PrimInt63.land (u32raw a) (PrimInt63.lxor (u32raw b) 4294967295)).
Definition u32_not    (a   : GoU32) : GoU32 := u32wrap (PrimInt63.lxor (u32raw a) 4294967295).
Definition u32_shl (x : GoU32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU32 := u32wrap (PrimInt63.land (PrimInt63.lsl (u32raw x) k) 4294967295).
Definition u32_shr (x : GoU32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoU32 := u32wrap (PrimInt63.lsr (u32raw x) k).
Definition u32_div (a b : GoU32) (_ : (PrimInt63.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (PrimInt63.divs (u32raw a) (u32raw b)).
Definition u32_mod (a b : GoU32) (_ : (PrimInt63.eqb (u32raw b) 0) = false) : GoU32 := u32wrap (PrimInt63.mods (u32raw a) (u32raw b)).
Definition int_of_u32 (x : GoU32) : int := u32raw x.
Definition u32_of_int (x : int) : GoU32 := u32wrap (PrimInt63.land x 4294967295).

(* [i32_norm] hoisted to the wrapper-record block (the GoI32 provenance invariant needs it).
   [i32wrap] = normalize + carry the trivial provenance proof, so [MkI32 5000000000 _] is
   unconstructable. *)
Definition i32wrap (x : int) : GoI32 := MkI32 (i32_norm x) (squash (ex_intro _ x eq_refl)).
Definition i32_lit (x : int) (_ : (Sint63.leb (-2147483648)%sint63 x && Sint63.ltb x 2147483648)%bool = true) : GoI32 := i32wrap x.
Definition i32_add (a b : GoI32) : GoI32 := i32wrap (PrimInt63.add (i32raw a) (i32raw b)).
Definition i32_sub (a b : GoI32) : GoI32 := i32wrap (PrimInt63.sub (i32raw a) (i32raw b)).
Definition i32_mul (a b : GoI32) : GoI32 := i32wrap (PrimInt63.mul (i32raw a) (i32raw b)).  (* low 32 bits exact, then sign-extend *)
Definition i32_eqb (a b : GoI32) : bool := PrimInt63.eqb (i32raw a) (i32raw b).
Definition i32_ltb (a b : GoI32) : bool := Sint63.ltb (i32raw a) (i32raw b).
Definition i32_leb (a b : GoI32) : bool := Sint63.leb (i32raw a) (i32raw b).

(** Direct [>] / [>=] / [!=] for the remaining fixed widths (u16/i16/u32/i32),
    completing Go's six comparison operators for EVERY integer type.  Same trivial
    pattern as u8/i8 (swapped [</<=], [negb (==)]) recognized by the generic [fw_is]. *)
Definition u16_gtb  (a b : GoU16) : bool := u16_ltb b a.
Definition u16_geb  (a b : GoU16) : bool := u16_leb b a.
Definition u16_neqb (a b : GoU16) : bool := negb (u16_eqb a b).
Definition i16_gtb  (a b : GoI16) : bool := i16_ltb b a.
Definition i16_geb  (a b : GoI16) : bool := i16_leb b a.
Definition i16_neqb (a b : GoI16) : bool := negb (i16_eqb a b).
Definition u32_gtb  (a b : GoU32) : bool := u32_ltb b a.
Definition u32_geb  (a b : GoU32) : bool := u32_leb b a.
Definition u32_neqb (a b : GoU32) : bool := negb (u32_eqb a b).
Definition i32_gtb  (a b : GoI32) : bool := i32_ltb b a.
Definition i32_geb  (a b : GoI32) : bool := i32_leb b a.
Definition i32_neqb (a b : GoI32) : bool := negb (i32_eqb a b).
Definition i32_and    (a b : GoI32) : GoI32 := i32wrap (i32_norm (PrimInt63.land (i32raw a) (i32raw b))).
Definition i32_or     (a b : GoI32) : GoI32 := i32wrap (i32_norm (PrimInt63.lor  (i32raw a) (i32raw b))).
Definition i32_xor    (a b : GoI32) : GoI32 := i32wrap (i32_norm (PrimInt63.lxor (i32raw a) (i32raw b))).
Definition i32_andnot (a b : GoI32) : GoI32 := i32wrap (i32_norm (PrimInt63.land (i32raw a) (PrimInt63.lxor (i32raw b) 4294967295))).
Definition i32_not    (a   : GoI32) : GoI32 := i32wrap (i32_norm (PrimInt63.lxor (i32raw a) 4294967295)).
Definition i32_shl (x : GoI32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI32 := i32wrap (i32_norm (PrimInt63.lsl (i32raw x) k)).
Definition i32_shr (x : GoI32) (k : int) (_ : (Sint63.leb 0 k) = true) : GoI32 := i32wrap (i32_norm (PrimInt63.asr (i32raw x) k)).
Definition i32_div (a b : GoI32) (_ : (PrimInt63.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (i32_norm (PrimInt63.divs (i32raw a) (i32raw b))).
Definition i32_mod (a b : GoI32) (_ : (PrimInt63.eqb (i32raw b) 0) = false) : GoI32 := i32wrap (i32_norm (PrimInt63.mods (i32raw a) (i32raw b))).
Definition int_of_i32 (x : GoI32) : int := i32raw x.
Definition i32_of_int (x : int) : GoI32 := i32wrap (i32_norm x).

(* Build-checked: u32/i32 are distinct, out-of-range constants unrepresentable. *)
Fail Definition u32_no_implicit (x : GoU32) : GoU32 := u32_add x (5 : int).
Fail Definition u32_const_oob   : GoU32 := u32_lit 5000000000 eq_refl.   (* >= 2^32 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint32 (SProp range proof). *)
Fail Definition u32_forged : GoU32 := MkU32 5000000000 (squash eq_refl).
(* Build-checked: the RAW int32 constructor cannot forge an out-of-range value (provenance proof false). *)
Fail Definition i32_forged : GoI32 := MkI32 5000000000 (squash (ex_intro _ 5000000000 eq_refl)).

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
(* [wrap64]/[in_i64]/[i64wrap] are hoisted to the wrapper-record block. *)
(* Smart literal: DEMANDS the constant fit int64 (Go's compile-time representability
   check); an out-of-range literal is unrepresentable ([i64_const_oob] Fail). *)
Definition i64_lit (z : Z) (pf : in_i64 z = true) : GoI64 := MkI64 z (squash pf).
Definition i64_add (a b : GoI64) : GoI64 := i64wrap (i64raw a + i64raw b).
Definition i64_sub (a b : GoI64) : GoI64 := i64wrap (i64raw a - i64raw b).
Definition i64_mul (a b : GoI64) : GoI64 := i64wrap (i64raw a * i64raw b).
(* Unary negation (Go's unary [-]): [-x] = [0 - x] with the same two's-complement wrap
   (so [-MININT = MININT]).  Lowers to the DIRECT prefix [-x], not the encoded [0 - x]. *)
Definition i64_neg (a : GoI64) : GoI64 := i64wrap (wrap64 (Z.opp (i64raw a))).
Definition i64_eqb (a b : GoI64) : bool := Z.eqb (i64raw a) (i64raw b).
Definition i64_ltb (a b : GoI64) : bool := Z.ltb (i64raw a) (i64raw b).
Definition i64_leb (a b : GoI64) : bool := Z.leb (i64raw a) (i64raw b).

(** ── GoI64 ARITHMETIC has the commutative-semiring CORE mod 2^64 (signed two's-complement) — the
    signed analogue of the GoU64 laws.  Key: the SIGNED [wrap64] preserves the residue mod 2^64
    ([wrap64_residue]: [wrap64 z ≡ z]), so it is a ring homomorphism — an inner [wrap64] is absorbed
    across `+` / `*` ([wrap64_idem_*]); the rest mirrors GoU64. ── *)
Lemma wrap64_residue : forall z,
  (wrap64 z mod 18446744073709551616 = z mod 18446744073709551616)%Z.
Proof.
  intro z. unfold wrap64. rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. ring.
Qed.
Lemma wrap64_eq_of_mod : forall a b,
  (a mod 18446744073709551616 = b mod 18446744073709551616)%Z -> wrap64 a = wrap64 b.
Proof.
  intros a b H. unfold wrap64. f_equal.
  rewrite Zplus_mod, H, <- Zplus_mod. reflexivity.
Qed.
Lemma wrap64_idem_add_r : forall a b, wrap64 (a + wrap64 b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_add_l : forall a b, wrap64 (wrap64 a + b) = wrap64 (a + b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zplus_mod, wrap64_residue, <- Zplus_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_r : forall a b, wrap64 (a * wrap64 b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.
Lemma wrap64_idem_mul_l : forall a b, wrap64 (wrap64 a * b) = wrap64 (a * b).
Proof. intros. apply wrap64_eq_of_mod. rewrite Zmult_mod, wrap64_residue, <- Zmult_mod. reflexivity. Qed.

Lemma i64_ext : forall x y : GoI64, i64raw x = i64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.
Lemma i64raw_add : forall a b, i64raw (i64_add a b) = wrap64 (i64raw a + i64raw b).
Proof. intros. reflexivity. Qed.
Lemma i64raw_mul : forall a b, i64raw (i64_mul a b) = wrap64 (i64raw a * i64raw b).
Proof. intros. reflexivity. Qed.

(** Keystone coding (break #1 foundation): a CONCRETE [nat] ↦ Go int64 ([GoI64]) coding with an HONEST
    round-trip.  An injection [nat ↪ GoI64] with a left inverse is IMPOSSIBLE ([GoI64] is finite), so the
    round-trip [keystone_prj (keystone_inj n) = n] holds ONLY for REPRESENTABLE [n] ([Z.of_nat n < 2^63]) —
    [keystone_roundtrip].  The concurrency Keystone bridge must be re-founded on THIS bounded fact, not the
    impossible unbounded [forall n, prj (inj n) = n] (see PROGRESS.md). *)
Definition keystone_inj (n : nat) : GoI64 := i64wrap (Z.of_nat n).
Definition keystone_prj (g : GoI64) : nat := Z.to_nat (i64raw g).
Lemma keystone_roundtrip : forall n,
  (Z.of_nat n < 9223372036854775808)%Z -> keystone_prj (keystone_inj n) = n.
Proof.
  intros n Hn. pose proof (Nat2Z.is_nonneg n) as Hpos.
  unfold keystone_prj, keystone_inj, i64wrap. cbn [i64raw]. unfold wrap64.
  rewrite Z.mod_small by lia.
  replace (Z.of_nat n + 9223372036854775808 - 9223372036854775808)%Z with (Z.of_nat n) by lia.
  apply Nat2Z.id.
Qed.
(** Representability predicate for the Keystone bridge: a value the [keystone] coding round-trips
    (fits a signed int64).  Defined here so the [Z]-scope stays in [builtins.v] (concurrency.v has no ZArith). *)
Definition Vrep64 (n : nat) : Prop := (Z.of_nat n < 9223372036854775808)%Z.
Lemma Vrep64_0 : Vrep64 0.
Proof. unfold Vrep64. cbn. lia. Qed.

Lemma i64_add_comm : forall a b, i64_add a b = i64_add b a.
Proof. intros. apply i64_ext. rewrite !i64raw_add, (Z.add_comm (i64raw a)). reflexivity. Qed.
Lemma i64_mul_comm : forall a b, i64_mul a b = i64_mul b a.
Proof. intros. apply i64_ext. rewrite !i64raw_mul, (Z.mul_comm (i64raw a)). reflexivity. Qed.
Lemma i64_add_assoc : forall a b c, i64_add a (i64_add b c) = i64_add (i64_add a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_add.
  rewrite wrap64_idem_add_r, wrap64_idem_add_l. f_equal. ring.
Qed.
Lemma i64_mul_assoc : forall a b c, i64_mul a (i64_mul b c) = i64_mul (i64_mul a b) c.
Proof.
  intros. apply i64_ext. rewrite !i64raw_mul.
  rewrite wrap64_idem_mul_r, wrap64_idem_mul_l. f_equal. ring.
Qed.
Lemma i64_mul_add_distr_l : forall a b c,
  i64_mul a (i64_add b c) = i64_add (i64_mul a b) (i64_mul a c).
Proof.
  intros. apply i64_ext. rewrite !i64raw_add, !i64raw_mul, !i64raw_add.
  rewrite wrap64_idem_mul_r, wrap64_idem_add_l, wrap64_idem_add_r. f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on (signed) GoI64 and [<=] is antisymmetric — the int64 analogue of
    the GoU64 order laws (pure [Z]-order + [i64_ext]). *)
Lemma i64_ltb_irrefl : forall a, i64_ltb a a = false.
Proof. intros. unfold i64_ltb. apply Z.ltb_irrefl. Qed.
Lemma i64_ltb_trans : forall a b c, i64_ltb a b = true -> i64_ltb b c = true -> i64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold i64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma i64_lt_trichotomy : forall a b, i64_ltb a b = true \/ a = b \/ i64_ltb b a = true.
Proof.
  intros a b. unfold i64_ltb. destruct (Z.lt_trichotomy (i64raw a) (i64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply i64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma i64_leb_antisym : forall a b, i64_leb a b = true -> i64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold i64_leb in *. apply i64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(* Integer absolute value.  Go has NO abs builtin for ints (only [math.Abs] for
   floats — and that needs an import), so it is written by hand with an [if] in
   VALUE position: [|a| = if a < 0 then -a else a].  Faithful across the WHOLE
   int64 range INCLUDING the [MININT] corner: [0 - MININT] is the exact [2^63],
   which [wrap64] lands back at [MININT] — exactly Go's two's-complement
   [0 - a] (the classic [abs(math.MinInt64) = math.MinInt64] overflow).  This is
   the canonical demo of the pure-function tail-match lowering (ladder 7b): the
   body's [if] is a value-position match, lowered to an [if]/[else] whose arms
   each [return]. *)
Definition i64_abs (a : GoI64) : GoI64 :=
  if i64_ltb a (i64wrap 0) then i64_sub (i64wrap 0) a else a.
(* DIV/MOD: Go truncates toward ZERO ([Z.quot]/[Z.rem]) — NOT Coq's flooring
   [Z.div]/[Z.modulo] (which give [-7/2 = -4]).  Evidence-carrying non-zero divisor
   (Go panics on /0).  [wrap64] lands the lone overflow case [MININT / -1 = MININT]
   (the exact quotient [2^63] wraps to [-2^63], Go's two's-complement behaviour). *)
Definition i64_div (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.quot (i64raw a) (i64raw b))).
Definition i64_mod (a b : GoI64) (_ : Z.eqb (i64raw b) 0%Z = false) : GoI64 := i64wrap (wrap64 (Z.rem (i64raw a) (i64raw b))).
(* BITWISE: Go int64 [& | ^ &^] and unary [^] on the 64-bit two's-complement value.
   [Z.land]/[lor]/[lxor]/[lnot] use infinite two's complement, which agrees on the
   low 64 bits; the result of in-range operands stays in range, so [wrap64] is the
   identity here (kept for uniformity).  Unary [^x = -x-1]. *)
Definition i64_and    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (i64raw b))).
Definition i64_or     (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lor  (i64raw a) (i64raw b))).
Definition i64_xor    (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.lxor (i64raw a) (i64raw b))).
Definition i64_andnot (a b : GoI64) : GoI64 := i64wrap (wrap64 (Z.land (i64raw a) (Z.lnot (i64raw b)))).
Definition i64_not    (a   : GoI64) : GoI64 := i64wrap (wrap64 (Z.lnot (i64raw a))).
(* SHIFTS: [<<] wraps mod 2^64 ([wrap64 . Z.shiftl]); [>>] is ARITHMETIC (sign-
   filling) for signed = [Z.shiftr] (floor toward -inf, in range).  Evidence-
   carrying non-negative count (Go panics on a negative shift). *)
Definition i64_shl (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (wrap64 (Z.shiftl (i64raw x) k)).
Definition i64_shr (x : GoI64) (k : Z) (_ : (0 <=? k)%Z = true) : GoI64 := i64wrap (Z.shiftr (i64raw x) k).

(* Build-checked: a constant that does not fit int64 is UNREPRESENTABLE (Go's
   constant-overflow compile error), and int64 does not implicitly mix with [int]. *)
Fail Definition i64_const_oob : GoI64 := i64_lit 9223372036854775808%Z eq_refl.  (* = 2^63 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range int64 (in_i64 proof false). *)
Fail Definition i64_forged : GoI64 := MkI64 9223372036854775808%Z (squash eq_refl).
Fail Definition i64_no_implicit (x : GoI64) : GoI64 := i64_add x (5 : int).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE (Go panics). *)
Fail Definition i64_div_zero : GoI64 := i64_div (i64_lit 1%Z eq_refl) (i64_lit 0%Z eq_refl) eq_refl.
Fail Definition i64_shl_neg  : GoI64 := i64_shl (i64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- GoU64: FULL-WIDTH unsigned 64-bit integer (Go spec "Numeric types") ----

    Carried by [Z], normalised into [[0, 2^64)] after every op by [wrapU64]
    (always non-negative — Z.modulo of a positive modulus is non-negative).
    Extraction erases the wrapper; a [GoU64] value is a Go [uint64], which wraps
    unsigned-natively at [2^64], so the emitted ops need no mask.

    Comparison uses [Z.ltb]/[Z.leb] on non-negative operands, which gives the
    unsigned order (Z order agrees with unsigned order for non-negative values).

    Division: [Z.div]/[Z.modulo] (floored) agree with Go's truncating uint64
    division since both dividend and divisor are non-negative (floor = truncate
    for non-negative).

    Bitwise: [Z.land]/[Z.lor]/[Z.lxor] on non-negative operands stay in
    [[0, 2^64)] — no mask needed.  [Z.lnot n = -(n+1)] is negative, so
    [wrapU64] brings it back to [2^64-1-n] (the 64-bit bitwise complement).
    [Z.land n (Z.lnot m)] for n ≥ 0 stays ≥ 0 (and < 2^64) — no wrap needed.

    Shifts: [<<] wraps mod [2^64] via [wrapU64 . Z.shiftl]; [>>] is LOGICAL
    (for unsigned, arithmetic = logical), so [Z.shiftr n k] is exact for n ≥ 0. *)
(* [in_u64]/[wrapU64] are hoisted to the wrapper-record block (the GoU64 range invariant needs them).
   [wrapU64 z = z mod 2^64] is always in range, so [u64wrap] carries the proof from one lemma; a forged
   [u64wrap (2^64) _] is unconstructable ([in_u64 (2^64)] is false). *)
Lemma in_u64_wrapU64 : forall z, in_u64 (wrapU64 z) = true.
Proof.
  intro z. unfold in_u64, wrapU64.
  pose proof (Z.mod_pos_bound z 18446744073709551616%Z ltac:(lia)) as [Hlo Hhi].
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Definition u64wrap (z : Z) : GoU64 := MkU64 (wrapU64 z) (squash (in_u64_wrapU64 z)).
(* [u64_lit z _]: a uint64 constant; the proof is a representability check
   (must be in [0, 2^64)); an out-of-range literal is unrepresentable. *)
Definition u64_lit (z : Z) (pf : in_u64 z = true) : GoU64 := MkU64 z (squash pf).
Definition u64_add (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a + u64raw b)).
Definition u64_sub (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a - u64raw b)).
(* Unary negation: [-x] mod 2^64 (so [-1 = 2^64-1]).  Lowers to the prefix [-x]. *)
Definition u64_neg (a : GoU64) : GoU64 := u64wrap (wrapU64 (Z.opp (u64raw a))).
Definition u64_mul (a b : GoU64) : GoU64 := u64wrap (wrapU64 (u64raw a * u64raw b)).
Definition u64_eqb (a b : GoU64) : bool := Z.eqb (u64raw a) (u64raw b).
Definition u64_ltb (a b : GoU64) : bool := Z.ltb (u64raw a) (u64raw b).
Definition u64_leb (a b : GoU64) : bool := Z.leb (u64raw a) (u64raw b).

(** ── GoU64 ARITHMETIC has the commutative-semiring CORE mod 2^64 — `+` and `*` are commutative,
    associative, and distributive — an algebraic-faithfulness check that the modelled uint64
    arithmetic has the expected structure (wraparound is a ring homomorphism Z → Z/2^64, so it
    preserves these).  Two [GoU64] with equal raw [Z] are EQUAL — the second (SProp range) field is
    proof-irrelevant ([u64_ext]) — so every law reduces to a [Z]-mod identity. ── *)
Lemma u64_ext : forall x y : GoU64, u64raw x = u64raw y -> x = y.
Proof. intros [rx px] [ry py] H. cbn in H. subst ry. reflexivity. Qed.

Lemma u64raw_add : forall a b, u64raw (u64_add a b) = wrapU64 (u64raw a + u64raw b).
Proof. intros. unfold u64_add, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.
Lemma u64raw_mul : forall a b, u64raw (u64_mul a b) = wrapU64 (u64raw a * u64raw b).
Proof. intros. unfold u64_mul, u64wrap. cbn. unfold wrapU64. apply Zmod_mod. Qed.

Lemma u64_add_comm : forall a b, u64_add a b = u64_add b a.
Proof. intros. apply u64_ext. rewrite !u64raw_add, (Z.add_comm (u64raw a)). reflexivity. Qed.
Lemma u64_mul_comm : forall a b, u64_mul a b = u64_mul b a.
Proof. intros. apply u64_ext. rewrite !u64raw_mul, (Z.mul_comm (u64raw a)). reflexivity. Qed.

Lemma u64_add_assoc : forall a b c, u64_add a (u64_add b c) = u64_add (u64_add a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_add. unfold wrapU64.
  rewrite Z.add_mod_idemp_r, Z.add_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_assoc : forall a b c, u64_mul a (u64_mul b c) = u64_mul (u64_mul a b) c.
Proof.
  intros. apply u64_ext. rewrite !u64raw_mul. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.mul_mod_idemp_l by (intro H; discriminate H).
  f_equal. ring.
Qed.
Lemma u64_mul_add_distr_l : forall a b c,
  u64_mul a (u64_add b c) = u64_add (u64_mul a b) (u64_mul a c).
Proof.
  intros. apply u64_ext. rewrite !u64raw_add, !u64raw_mul, !u64raw_add. unfold wrapU64.
  rewrite Z.mul_mod_idemp_r, Z.add_mod_idemp_l, Z.add_mod_idemp_r by (intro H; discriminate H).
  f_equal. ring.
Qed.

(** [<] is a STRICT TOTAL ORDER on GoU64 (irreflexive, transitive, trichotomous) and [<=] is
    antisymmetric — Go's comparison operators on uint64 are a well-behaved total order, a
    completeness check the value-witnesses don't give.  (Pure [Z]-order + [u64_ext]; the SProp range
    field is never needed.) *)
Lemma u64_ltb_irrefl : forall a, u64_ltb a a = false.
Proof. intros. unfold u64_ltb. apply Z.ltb_irrefl. Qed.
Lemma u64_ltb_trans : forall a b c, u64_ltb a b = true -> u64_ltb b c = true -> u64_ltb a c = true.
Proof. intros a b c Hab Hbc. unfold u64_ltb in *. apply Z.ltb_lt in Hab, Hbc. apply Z.ltb_lt. lia. Qed.
Lemma u64_lt_trichotomy : forall a b, u64_ltb a b = true \/ a = b \/ u64_ltb b a = true.
Proof.
  intros a b. unfold u64_ltb. destruct (Z.lt_trichotomy (u64raw a) (u64raw b)) as [H|[H|H]].
  - left. apply Z.ltb_lt. exact H.
  - right; left. apply u64_ext. exact H.
  - right; right. apply Z.ltb_lt. exact H.
Qed.
Lemma u64_leb_antisym : forall a b, u64_leb a b = true -> u64_leb b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold u64_leb in *. apply u64_ext.
  apply Z.le_antisymm; apply Z.leb_le; assumption.
Qed.

(** Direct [>] / [>=] / [!=] completing Go's six comparison operators for the
    canonical [int64]/[uint64].  We already emit [== < <=] directly; [>]/[>=] are the
    swapped [</<=] and [!=] is [negb (==)] — SEMANTICALLY identical to the encodings a
    program would otherwise write, but each is recognized by name and lowered to the
    DIRECT Go operator ([a > b], not [b < a]), so the emitted Go matches the source
    operator.  (The [int64] order is signed, the [uint64] order unsigned, inherited
    from [i64_ltb]/[u64_ltb].) *)
Definition i64_gtb  (a b : GoI64) : bool := i64_ltb b a.
Definition i64_geb  (a b : GoI64) : bool := i64_leb b a.
Definition i64_neqb (a b : GoI64) : bool := negb (i64_eqb a b).
Definition u64_gtb  (a b : GoU64) : bool := u64_ltb b a.
Definition u64_geb  (a b : GoU64) : bool := u64_leb b a.
Definition u64_neqb (a b : GoU64) : bool := negb (u64_eqb a b).
(* DIVISION: evidence-carrying non-zero divisor (Go panics on /0).  [Z.div] and
   [Z.modulo] are used here (floored) — for non-negative values they agree with
   Go's truncating division, so the result is exact.  No wrap needed: both
   results stay in [[0, 2^64)]. *)
Definition u64_div (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.div    (u64raw a) (u64raw b)).
Definition u64_mod (a b : GoU64) (_ : Z.eqb (u64raw b) 0%Z = false) : GoU64 := u64wrap (Z.modulo (u64raw a) (u64raw b)).
Definition u64_and    (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (u64raw b)).
Definition u64_or     (a b : GoU64) : GoU64 := u64wrap (Z.lor  (u64raw a) (u64raw b)).
Definition u64_xor    (a b : GoU64) : GoU64 := u64wrap (Z.lxor (u64raw a) (u64raw b)).
Definition u64_andnot (a b : GoU64) : GoU64 := u64wrap (Z.land (u64raw a) (Z.lnot (u64raw b))).
Definition u64_not    (a   : GoU64) : GoU64 := u64wrap (wrapU64 (Z.lnot (u64raw a))).
Definition u64_shl (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (wrapU64 (Z.shiftl (u64raw x) k)).
Definition u64_shr (x : GoU64) (k : Z) (_ : (0 <=? k)%Z = true) : GoU64 := u64wrap (Z.shiftr (u64raw x) k).

(* Build-checked: a constant >= 2^64 is UNREPRESENTABLE; uint64 does not
   implicitly mix with [int], [GoI64], or other types. *)
Fail Definition u64_const_oob : GoU64 := u64_lit 18446744073709551616%Z eq_refl.  (* = 2^64 *)
(* Build-checked: the RAW constructor cannot forge an out-of-range uint64 (in_u64 proof false). *)
Fail Definition u64_forged : GoU64 := MkU64 18446744073709551616%Z (squash eq_refl).
Fail Definition u64_no_implicit (x : GoU64) : GoU64 := u64_add x (5 : int).
(* Build-checked: a ZERO divisor / NEGATIVE shift count is UNREPRESENTABLE. *)
Fail Definition u64_div_zero : GoU64 := u64_div (u64_lit 1%Z eq_refl) (u64_lit 0%Z eq_refl) eq_refl.
Fail Definition u64_shl_neg  : GoU64 := u64_shl (u64_lit 1%Z eq_refl) (-1)%Z eq_refl.

(** ---- Bitwise BOOLEAN-ALGEBRA laws for GoU64 (the bitwise counterpart of the proven arithmetic
    semiring + total-order laws).  COMMUTATIVITY holds directly; ASSOCIATIVITY needs that [wrapU64]
    (mod 2⁶⁴) depends only on the LOW 64 bits — so an inner [wrapU64] under a bit-op can be pulled out
    ([wrapU64_bit_r]/[_l], one [Z.bits_inj'] each).  (Idempotence [a & a = a] is SProp-BLOCKED: it
    needs [u64raw a] in range, which the [Squash] seal hides from [Prop] — documented, not skipped.) *)
Lemma wrapU64_bit_r : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op a (wrapU64 b)) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma wrapU64_bit_l : forall (op : Z -> Z -> Z) (bf : bool -> bool -> bool),
  (forall x y n, Z.testbit (op x y) n = bf (Z.testbit x n) (Z.testbit y n)) ->
  forall a b, wrapU64 (op (wrapU64 a) b) = wrapU64 (op a b).
Proof.
  intros op bf Hspec a b. unfold wrapU64. change 18446744073709551616%Z with (2 ^ 64)%Z.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Hspec.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma u64_and_comm : forall a b, u64_and a b = u64_and b a.
Proof. intros a b. apply u64_ext. unfold u64_and, u64wrap; cbn. f_equal. apply Z.land_comm. Qed.
Lemma u64_or_comm  : forall a b, u64_or a b = u64_or b a.
Proof. intros a b. apply u64_ext. unfold u64_or, u64wrap; cbn. f_equal. apply Z.lor_comm. Qed.
Lemma u64_xor_comm : forall a b, u64_xor a b = u64_xor b a.
Proof. intros a b. apply u64_ext. unfold u64_xor, u64wrap; cbn. f_equal. apply Z.lxor_comm. Qed.

Lemma u64_and_assoc : forall a b c, u64_and a (u64_and b c) = u64_and (u64_and a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_and, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.land andb Z.land_spec), (wrapU64_bit_l Z.land andb Z.land_spec).
  f_equal. apply Z.land_assoc.
Qed.
Lemma u64_or_assoc : forall a b c, u64_or a (u64_or b c) = u64_or (u64_or a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_or, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lor orb Z.lor_spec), (wrapU64_bit_l Z.lor orb Z.lor_spec).
  f_equal. apply Z.lor_assoc.
Qed.
Lemma u64_xor_assoc : forall a b c, u64_xor a (u64_xor b c) = u64_xor (u64_xor a b) c.
Proof.
  intros a b c. apply u64_ext. unfold u64_xor, u64wrap; cbn.
  rewrite (wrapU64_bit_r Z.lxor xorb Z.lxor_spec), (wrapU64_bit_l Z.lxor xorb Z.lxor_spec).
  f_equal. symmetry. apply Z.lxor_assoc.
Qed.

(** ---- A4.2: GoI64 / GoU64 are THE canonical Go int64 / uint64 ----

    [GoI64]/[GoU64] (the [Z]-carried full-width types) are the faithful models of
    Go's [int64]/[uint64] (Go spec "Numeric types"); the bounded [Sint63] [int] is
    relegated to proof-layer / compile-time-index use.  These abbreviations + scopes
    make the full-width types as ERGONOMIC as a primitive: [42%i64] is a range-checked
    int64 literal, [(a + b)%i64] is full-width addition.

    The literal parser ([i64_of_Z]/[u64_of_Z]) RANGE-CHECKS at PARSE TIME, returning
    [None] for an out-of-range numeral — so an over-wide literal is REJECTED by the
    parser, exactly Go's untyped-constant overflow compile error (the A5 gap, closed
    for int64/uint64 LITERALS here; constant ARITHMETIC at arbitrary precision is still
    A5).  This is why the literal builds the raw [MkI64]/[MkU64]: the parser's range
    check is the proof, so no separate [_lit] obligation is needed. *)
Notation int64  := GoI64.
Notation uint64 := GoU64.

Definition i64_of_Z (z : Z) : option GoI64 := if in_i64 z then Some (i64wrap z) else None.  (* wrap64 z = z under the guard *)
Definition Z_of_i64 (x : GoI64) : Z := i64raw x.
Definition u64_of_Z (z : Z) : option GoU64 := if in_u64 z then Some (u64wrap z) else None.  (* wrapU64 z = z under the guard *)
Definition Z_of_u64 (x : GoU64) : Z := u64raw x.

Declare Scope i64_scope.
Delimit Scope i64_scope with i64.
Bind Scope i64_scope with GoI64.
Number Notation GoI64 i64_of_Z Z_of_i64 : i64_scope.
Infix "+"  := i64_add : i64_scope.
Infix "-"  := i64_sub : i64_scope.
Infix "*"  := i64_mul : i64_scope.
Infix "=?" := i64_eqb : i64_scope.
Infix "<?" := i64_ltb : i64_scope.
Infix "<=?" := i64_leb : i64_scope.

Declare Scope u64_scope.
Delimit Scope u64_scope with u64.
Bind Scope u64_scope with GoU64.
Number Notation GoU64 u64_of_Z Z_of_u64 : u64_scope.
Infix "+"  := u64_add : u64_scope.
Infix "-"  := u64_sub : u64_scope.
Infix "*"  := u64_mul : u64_scope.
Infix "=?" := u64_eqb : u64_scope.
Infix "<?" := u64_ltb : u64_scope.
Infix "<=?" := u64_leb : u64_scope.

(* Build-checked: an out-of-range literal is REJECTED AT PARSE (Go untyped-constant
   overflow).  [2^63] overflows int64 (max [2^63-1]); [2^64] overflows uint64. *)
Fail Definition i64_lit_oob : GoI64 := (9223372036854775808)%i64.   (* = 2^63 *)
Fail Definition u64_lit_oob : GoU64 := (18446744073709551616)%u64.  (* = 2^64 *)

(** ---- Full-width int64 <-> uint64 CONVERSIONS (Go spec "Conversions") ----
    Go's [uint64(x)] / [int64(x)] between the two 64-bit integer types REINTERPRET
    the same 64-bit two's-complement pattern: the value is unchanged when it fits
    the target, otherwise it is the mod-2^64 representative (a negative int64 maps to
    its 2^64-complement uint64; a uint64 >= 2^63 maps to a negative int64).  The
    Z-carried model makes this EXACT — re-normalise the raw [Z] into the target's
    range — with NO rounding or loss (unlike int<->float).  [int_of_FW]/[FW_of_int]
    cover the NARROW widths; these are the full-width pair (distinct because [GoU64]
    lowers to a real Go [uint64], not [int64]). *)
Definition u64_of_i64 (a : GoI64) : GoU64 := u64wrap (wrapU64 (i64raw a)).
Definition i64_of_u64 (a : GoU64) : GoI64 := i64wrap (wrap64  (u64raw a)).

(* Reinterpret is mod-2^64 on both sides, so the two normalisers AGREE after a
   round-trip: [wrap64 (wrapU64 z) = wrap64 z] (both reduce mod 2^64 first). *)
Lemma wrap64_wrapU64 : forall z, wrap64 (wrapU64 z) = wrap64 z.
Proof.
  intro z. unfold wrap64, wrapU64.
  rewrite Zplus_mod_idemp_l.   (* (z mod 2^64 + 2^63) mod 2^64 = (z + 2^63) mod 2^64 *)
  reflexivity.
Qed.

(** SIGNED↔UNSIGNED bitwise FAITHFULNESS — Go: [a & b == int64(uint64(a) & uint64(b))].
    The signed bitwise op equals the SIGNED REINTERPRETATION of the UNSIGNED op on the two's-complement
    bit patterns, so [i64_and]/[_or]/[_xor] are FAITHFUL to Go's int64/uint64 bitwise agreement.  Proof:
    cancel the double mod-2⁶⁴ ([wrapU64_idem]), pull each [wrapU64] out through the bit-op
    ([wrapU64_bit_l]/[_r]), then collapse [wrap64 ∘ wrapU64 = wrap64]. *)
Lemma wrapU64_idem : forall z, wrapU64 (wrapU64 z) = wrapU64 z.
Proof. intro z. unfold wrapU64. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma i64_and_via_u64 : forall a b,
  i64_and a b = i64_of_u64 (u64_and (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_and i64_of_u64 u64_and u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.land andb Z.land_spec), (wrapU64_bit_r Z.land andb Z.land_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_or_via_u64 : forall a b,
  i64_or a b = i64_of_u64 (u64_or (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_or i64_of_u64 u64_or u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lor orb Z.lor_spec), (wrapU64_bit_r Z.lor orb Z.lor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.
Lemma i64_xor_via_u64 : forall a b,
  i64_xor a b = i64_of_u64 (u64_xor (u64_of_i64 a) (u64_of_i64 b)).
Proof.
  intros a b. apply i64_ext.
  cbn [i64_xor i64_of_u64 u64_xor u64_of_i64 i64wrap u64wrap i64raw u64raw].
  rewrite !wrapU64_idem,
          (wrapU64_bit_l Z.lxor xorb Z.lxor_spec), (wrapU64_bit_r Z.lxor xorb Z.lxor_spec),
          wrap64_wrapU64.
  reflexivity.
Qed.

(** ---- A5: untyped INTEGER constants (Go spec "Constants") ----

    A Go untyped constant is ARBITRARY-PRECISION: constant arithmetic is exact (no
    width, no wrap), and the constant acquires a fixed-width TYPE only at the point of
    USE, where a representability check fires — a constant that does not fit is a
    COMPILE ERROR, not a runtime wrap.  We model an untyped int constant as [Z], its
    arithmetic as [Z] arithmetic (exact), and the type-at-use conversion as
    [i64c]/[u64c]: each EVALUATES the closed [Z] expression with [vm_compute] (real
    bignums, so an INTERMEDIATE may exceed the target width — e.g. [1 << 70] — as long
    as the final value fits) to a literal, then converts demanding [in_i64]/[in_u64].
    An out-of-range constant FAILS to elaborate (the [now vm_compute] proof of
    representability cannot be built) — the analog of Go's untyped-constant overflow.
    The literal the notation produces lowers via the existing [i64_lit]/[u64_lit] fold;
    no plugin change — the arbitrary precision lives entirely in [vm_compute]. *)
Notation i64c e :=
  (i64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).
Notation u64c e :=
  (u64_lit ltac:(let v := eval vm_compute in (e : Z) in exact v) ltac:(now vm_compute))
  (only parsing).

(** ---- int64 → float64 conversion (Go spec "Conversions", Phase D) ----

    Go [float64(i)] converts an [int64] to an IEEE double; values past 2^53 ROUND (the
    double's mantissa), exactly as Go does.  [PrimFloat.of_uint63] converts a uint63
    MAGNITUDE to a double; the [Z]-carried signed [GoI64] splits the sign.  *PROOF-ONLY*
    (machine-checked by [f64_of_i64_pos]/[f64_of_i64_neg] in main.v): the sign-split makes
    the body a value-position [if], which the plugin cannot yet lower (the ladder-7b
    value-position-match gap), so it is NOT extracted — the intended lowering is Go
    [float64(i)] once that gap closes.  *Boundary:* float64→int64 TRUNCATION — [PrimFloat]
    has no truncation primitive, so [int64(f)] cannot be modeled here (a [math.Abs]/
    [math.Sqrt]-style boundary). *)
Definition f64_of_i64 (a : GoI64) : float :=
  if Z.leb 0 (i64raw a)
  then PrimFloat.of_uint63 (Uint63.of_Z (i64raw a))
  else PrimFloat.opp (PrimFloat.of_uint63 (Uint63.of_Z (Z.opp (i64raw a)))).

(** int64 → narrow (Go [uint8(x)] / [int8(x)] / … / [int32(x)]): TRUNCATE to the low W bits.
    A [GoU8]/[GoI8]/… erases to the same int64 carrier as a [GoI64], so the conversion is
    EXACTLY the narrow-from-int truncation ([fw_wrap]: mask to W bits, sign-extend for [iN]) —
    lowered to Go's native [(x & 0xFF)] / sign-extended form, identical to [uN_of_int].  The
    model crosses the [Z] carrier of [GoI64] into the int63 carrier via [Uint63.of_Z], then
    masks: since [2^W | 2^63] the low W bits of [(i64raw a) mod 2^63] ARE [(i64raw a) mod 2^W]
    (faithful for W < 63).  The [of_Z]-match body never reaches the emitted Go — the op is
    recognized by name (`fw_is r "of_i64"`) and its decl suppressed (`fixed_width_op`), exactly
    as the [of_int] narrows are.  Mirrors each [uN_of_int]/[iN_of_int] structure so it stays a
    NAMED call the recognizer fires on (not force-inlined). *)
Definition u8_of_i64  (a : GoI64) : GoU8  := u8wrap (PrimInt63.land (Uint63.of_Z (i64raw a)) 255).
Definition i8_of_i64  (a : GoI64) : GoI8  := i8wrap (i8_norm  (Uint63.of_Z (i64raw a))).
Definition u16_of_i64 (a : GoI64) : GoU16 := u16wrap (PrimInt63.land (Uint63.of_Z (i64raw a)) 65535).
Definition i16_of_i64 (a : GoI64) : GoI16 := i16wrap (i16_norm (Uint63.of_Z (i64raw a))).
Definition u32_of_i64 (a : GoI64) : GoU32 := u32wrap (PrimInt63.land (Uint63.of_Z (i64raw a)) 4294967295).
Definition i32_of_i64 (a : GoI64) : GoI32 := i32wrap (i32_norm (Uint63.of_Z (i64raw a))).

(** int → float64 (Go [float64(i)]): the IEEE double NEAREST the integer (EXACT for
    |i| < 2^53, rounds beyond — exactly Go's rule).  [PrimFloat.of_uint63] converts the
    unsigned MAGNITUDE; the sign-split handles negatives ([0 - i] is the two's-complement
    magnitude of a negative [i], then negate the float).  Unlike [f64_of_i64] (whose [Z]
    carrier needs the match-bodied [Uint63.of_Z]), the index [int] (Sint63) IS already an
    int63, so it passes STRAIGHT to [of_uint63] — only that one leaf primitive sits in the
    body.  Recognized by name → native [float64(i)]; the body (the sign-split + [of_uint63])
    is suppressed, so it never reaches the emitted Go.  Machine-checked by [f64_of_int_pos]/
    [f64_of_int_neg] (main.v).  Returns [float] (not a record), so no unbox-renaming collapse
    — it stays a NAMED call the recognizer fires on. *)
Definition f64_of_int (i : int) : float :=
  if Sint63.ltb i 0%sint63
  then PrimFloat.opp (PrimFloat.of_uint63 (PrimInt63.sub 0%uint63 i))
  else PrimFloat.of_uint63 i.

(** float64 → int64 (Go [int64(f)]): TRUNCATE toward zero.  Built on the stdlib's VERIFIED
    decomposition [Prim2SF f] — a finite [f = (-1)^s * m * 2^e] ([m] positive, [e : Z]).  The
    truncated MAGNITUDE is [m * 2^e] when [e >= 0] (an exact integer) or [m / 2^(-e)] when
    [e < 0] (the FLOOR of the positive magnitude = truncation toward zero); the sign is
    applied AFTER, so the whole thing rounds toward zero — exactly Go's rule.  MODELED +
    machine-checked (witnesses in main.v).  *Runtime lowering DEFERRED (proof-only, not
    reachable from [main_effect], so not extracted):* the intended lowering is the native
    [int64(f)], but [i64_of_f64] returns [GoI64] (a single-field record), so its Z-from-
    [Prim2SF] body hits the SAME wall as the narrow→int64 widening — the [MkI64] unbox + a
    match-bodied Z computation lets Coq's case-of-case fusion inline the [match] into VALUE
    position, regardless of [NoInline] or splitting out [f64_trunc_Z].  (The int→float casts
    [f64_of_int]/[f64_of_i64] DO lower — they return [float], a PRIMITIVE, not a record.)
    *Bounded deviation:* NaN / ±Inf / out-of-int64-range inputs are
    IMPLEMENTATION-DEFINED in Go (spec "Conversions"); the model gives [0] (and [wrap64] folds
    overflow), so those corners are a documented model gap — the FINITE in-range case (the
    common use) is faithful and machine-checked. *)
Definition f64_trunc_Z (f : float) : Z :=
  match Prim2SF f with
  | S754_finite s m e =>
      let mag := if Z.leb 0 e then (Zpos m * 2 ^ e)%Z else (Zpos m / 2 ^ (- e))%Z in
      if s then (- mag)%Z else mag
  | _ => 0%Z
  end.
(* The [match]-on-[Prim2SF] lives in [f64_trunc_Z] (returns [Z]); [i64_of_f64]'s body is then
   [wrap64 (…)] — a function application, NOT a match — so Coq's case-of-case fusion has no
   match-of-match to inline, and [i64_of_f64] stays a NAMED call the recognizer fires on. *)
Definition i64_of_f64 (f : float) : GoI64 := i64wrap (wrap64 (f64_trunc_Z f)).

(** float64 → uint64 (Go [uint64(f)]): TRUNCATE toward zero — the exact parallel of [i64_of_f64],
    only wrapping into the unsigned range.  In-range ([0 <= trunc f < 2^64]) it is faithful (the
    verified [f64_trunc_Z]); out of range is Go-implementation-defined, where the defined wrap is
    an acceptable choice.  Lowered to native [uint64(f)]; the [Prim2SF]-match body suppressed. *)
Definition u64_of_f64 (f : float) : GoU64 := u64wrap (wrapU64 (f64_trunc_Z f)).

(** uint64 → float64 (Go [float64(v)]): the CORRECTLY-ROUNDED double.  [PrimFloat.of_uint63] only
    takes a 63-bit input, so values in [[2^63, 2^64)] cannot go through it directly.  The standard
    round-to-odd trick handles them EXACTLY: halve ([v >> 1], now < 2^63) but OR the lost bit back
    in ([| (v & 1)]) as a sticky bit, round THAT to binary64, then double (exact — a power-of-two
    scale, no second rounding).  The sticky low bit makes the single rounding of [v>>1|v&1] land
    the same way a direct rounding of [v] would (round-nearest-even preserved).  Below 2^63 it is
    the plain [of_uint63].  Lowered to native [float64(v)]; the split/trick body suppressed. *)
Definition f64_of_u64 (a : GoU64) : float :=
  if Z.ltb (u64raw a) 9223372036854775808%Z   (* < 2^63 ⇒ fits the 63-bit [of_uint63] directly *)
  then PrimFloat.of_uint63 (Uint63.of_Z (u64raw a))
  else PrimFloat.mul
         (PrimFloat.of_uint63 (Uint63.of_Z (Z.lor (Z.shiftr (u64raw a) 1) (Z.land (u64raw a) 1))))
         2.

(** UNTYPED FLOAT CONSTANTS — exact rationals, rounded ONCE at the typed boundary.  Go folds
    constant float arithmetic at ARBITRARY precision, rounding only when the constant acquires a
    type: [const x float64 = 0.1 + 0.2] is [float64(3/10) = 0.3] EXACTLY, NOT the runtime
    [0.1+0.2 = 0.30000000000000004] (which rounds each operand THEN adds).  Fido's runtime floats
    ([PrimFloat]) give the runtime answer; this models the CONSTANT one.  An [FConst] is an exact
    rational [num/den]; [fc_add]/[fc_sub]/[fc_mul] are EXACT ([Q]-style cross-multiply, no
    rounding); [f64_of_fconst] rounds to [float64] exactly ONCE — an IEEE divide of the two
    integer endpoints, which is correctly-rounded while [|num|, den < 2^53] (both endpoints exact,
    so the single division carries the only rounding).  *MODEL + machine-checked; LOWERING (a
    plugin FConst-fold → Go [float64(num)/float64(den)], which Go re-folds to the same constant)
    is the deferred follow-on.* *)
(** The denominator is a [positive] — exactly the shape of Coq's [QArith.Q] — so a Go
    float CONSTANT is an EXACT *nonzero-denominator* rational and can NEVER denote ±Inf
    or NaN (review #6 P2 #16).  A malformed [den = 0] constant is now UNCONSTRUCTABLE by
    type, so the extractor's [den = 0] fold guard is a dead defensive boundary rather than
    a reachable path.  [Bind Scope] keeps [mkFC n d] literals parsing [d] as a positive. *)
Record FConst := mkFC { fc_num : Z ; fc_den : positive }.
Bind Scope positive_scope with positive.
Definition fc_add (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) + fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_sub (a b : FConst) : FConst :=
  mkFC (fc_num a * Zpos (fc_den b) - fc_num b * Zpos (fc_den a)) (Pos.mul (fc_den a) (fc_den b)).
Definition fc_mul (a b : FConst) : FConst := mkFC (fc_num a * fc_num b) (Pos.mul (fc_den a) (fc_den b)).
(** Constant DIVISION is EVIDENCE-CARRYING: Go constant division by zero is a COMPILE error,
    so [fc_div] DEMANDS a proof the divisor's numerator is nonzero — a constant [/0] cannot be
    written (review #6 P2 #16; min-suite #12).  The denominator stays strictly positive by
    folding the divisor's SIGN into the numerator:
      (na/da)/(nb/db) = (na·db)/(da·nb) = (sgn(nb)·na·db)/(da·|nb|). *)
Definition fc_div (a b : FConst) (hb : fc_num b <> 0%Z) : FConst :=
  mkFC (Z.sgn (fc_num b) * fc_num a * Zpos (fc_den b))
       (Pos.mul (fc_den a) (Z.to_pos (Z.abs (fc_num b)))).  (* (a/b)/(c/d) = ad/bc, den kept > 0 *)
(** Exact integer → [spec_float] (NO rounding): mantissa = [|z|], exponent 0.  Shared by the exact
    rational → float conversions (binary64 here; binary32 for [f32_of_fconst]). *)
Definition sf_of_Z (z : Z) : spec_float :=
  match z with
  | Z0     => S754_zero false
  | Zpos p => S754_finite false p 0
  | Zneg p => S754_finite true  p 0
  end.
(** Exact float CONSTANT → float64 — round the EXACT rational [num/den] ONCE to binary64 via [SFdiv]
    of the EXACT-integer spec_floats (no intermediate binary64), so correctly-rounded for ALL num/den,
    not just [< 2^53].  Lowered to Go [float64(num.0 / den.0)] (untyped-constant division, single
    round).  (The old [div (f64_of_i64 num) (f64_of_i64 den)] DOUBLE-rounds when both endpoints exceed
    2^53 — a latent model unsoundness, only masked at extraction by a fail-loud 2^53 guard.) *)
Definition f64_of_fconst (a : FConst) : float :=
  SF2Prim (SFdiv 53 1024 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a)))).

(** FLOAT32 arithmetic — faithful binary32 (prec 24, emax 128) via [SpecFloat], then routed
    back through [f32_of_f64] so the result re-enters the abstract type WITH its provenance
    proof ([eq_refl]).  The extra round is the IDENTITY in reality (an [SFadd]/… result is
    already in binary32 format), so this stays faithful — exactly Go's [float32] arithmetic
    (single round-to-nearest-even at binary32).  Lowered BY NAME to native Go [float32]
    [+]/[-]/[*]/[/]; the SpecFloat body (and the [f32val]/[mkF32] wrapping) is suppressed. *)
Definition f32_add (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SF2Prim (SFadd 24 128 (Prim2SF (f32val x)) (Prim2SF (f32val y)))).
Definition f32_sub (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SF2Prim (SFsub 24 128 (Prim2SF (f32val x)) (Prim2SF (f32val y)))).
Definition f32_mul (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SF2Prim (SFmul 24 128 (Prim2SF (f32val x)) (Prim2SF (f32val y)))).
Definition f32_div (x y : GoFloat32) : GoFloat32 :=
  f32_of_f64 (SF2Prim (SFdiv 24 128 (Prim2SF (f32val x)) (Prim2SF (f32val y)))).

(** float32 COMPARISON.  The carrier holds a binary32-representable value and a comparison
    performs NO rounding, so binary32 and binary64 ordering agree exactly on the carriers —
    hence [PrimFloat.ltb]/[leb]/[eqb] on [f32val] ARE the float32 comparisons.  Lowered to
    native Go [float32] [<]/[<=]/[==]/[>]/[>=]/[!=] (the operands are [float32]).  Same NaN
    subtlety as float64: [f32_geb]/[f32_gtb] are the SWAPPED [leb]/[ltb] (so a NaN operand
    makes [>=]/[>] FALSE, matching Go/IEEE), while [f32_neqb] is [negb (eqb)]. *)
Definition f32_ltb  (x y : GoFloat32) : bool := PrimFloat.ltb (f32val x) (f32val y).
Definition f32_leb  (x y : GoFloat32) : bool := PrimFloat.leb (f32val x) (f32val y).
Definition f32_eqb  (x y : GoFloat32) : bool := PrimFloat.eqb (f32val x) (f32val y).
Definition f32_gtb  (x y : GoFloat32) : bool := PrimFloat.ltb (f32val y) (f32val x).
Definition f32_geb  (x y : GoFloat32) : bool := PrimFloat.leb (f32val y) (f32val x).
Definition f32_neqb (x y : GoFloat32) : bool := negb (PrimFloat.eqb (f32val x) (f32val y)).

(** float32 → float64 WIDENING is EXACT (a binary32 value is exactly a binary64): identity on
    the carrier — SOUND precisely because [f32ok] guarantees the carrier is binary32-representable
    (the carrier equals its own [f32_round]).  Lowered to Go [float64(x)].  (Narrowing
    [f32_of_f64] / [f32_lit] is defined up top, with the type.) *)
Definition f64_of_f32 (x : GoFloat32) : GoFloat64 := f32val x.

(** DIRECT integer → float32 (Go [float32(x)]) — round the EXACT integer ONCE to binary32 via
    [binary_normalize] at format (24, 128).  This is NOT [f32_of_f64 (f64_of_int x)] (= Go
    [float32(float64(x))]): for |x| > 2^53 the int→float64 step ALREADY rounds, and the second
    round to binary32 can DISAGREE — double rounding.  (E.g. [x = 2^61 + 2^37 + 1]: direct rounds
    UP to [2^61 + 2^38]; via float64 the low bit is lost onto the float32 midpoint and ties-to-even
    rounds DOWN to [2^61].)  Lowered to Go's direct [float32(x)] cast (single round). *)
Definition f32_of_i64 (a : GoI64) : GoFloat32 :=
  f32_of_f64 (SF2Prim (binary_normalize 24 128 (i64raw a) 0 false)).
Definition f32_of_u64 (a : GoU64) : GoFloat32 :=
  f32_of_f64 (SF2Prim (binary_normalize 24 128 (u64raw a) 0 false)).
Definition f32_of_int (i : GoInt) : GoFloat32 :=
  f32_of_f64 (SF2Prim (binary_normalize 24 128 (Sint63.to_Z i) 0 false)).

(** DIRECT exact float CONSTANT → float32 (Go [float32(num.0 / den.0)]): round the EXACT rational
    [num/den] ONCE to binary32 via [SFdiv] of the EXACT-integer spec_floats (no intermediate binary64
    — so correct for ALL [num], [den], unlike [f32_of_f64 (f64_of_fconst …)] which double-rounds when
    [|num| > 2^53]: e.g. [2305843146652647425/1] rounds to [2^61+2^38] here but [2^61] via float64).
    [SFdiv] handles arbitrary mantissas, so this is the correctly-rounded rational→binary32. *)
Definition f32_of_fconst (a : FConst) : GoFloat32 :=
  f32_of_f64 (SF2Prim (SFdiv 24 128 (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a))))).

(** float32 unary NEGATION — EXACT (IEEE sign-flip, makes [-0.0]); re-enter the abstract type
    (the round is the identity on the sign-flipped, still-representable value).  Lowered to Go
    [-x].  Same role as [PrimFloat.opp] for float64. *)
Definition f32_neg (x : GoFloat32) : GoFloat32 := f32_of_f64 (PrimFloat.opp (f32val x)).

(** [min]/[max] on float32 (Go "min and max") — the SAME two IEEE corners as float64, decided on
    the binary32 carriers: NaN propagation ([eqb v v = false]) and signed zero ([min(-0,+0) = -0],
    [max(-0,+0) = +0], via [1/v]).  Each returns the chosen OPERAND, already a valid [GoFloat32],
    so there is no re-rounding.  Lowered to Go [min]/[max] on float32. *)
Definition f32_min (x y : GoFloat32) : GoFloat32 :=
  if negb (PrimFloat.eqb (f32val x) (f32val x)) then x            (* x is NaN → NaN *)
  else if negb (PrimFloat.eqb (f32val y) (f32val y)) then y       (* y is NaN → NaN *)
  else if PrimFloat.ltb (f32val x) (f32val y) then x
  else if PrimFloat.ltb (f32val y) (f32val x) then y
  else if PrimFloat.eqb (f32val x) 0
       then (if PrimFloat.ltb (PrimFloat.div 1 (f32val x)) 0 then x else y)   (* min wants -0 *)
       else x.
Definition f32_max (x y : GoFloat32) : GoFloat32 :=
  if negb (PrimFloat.eqb (f32val x) (f32val x)) then x
  else if negb (PrimFloat.eqb (f32val y) (f32val y)) then y
  else if PrimFloat.ltb (f32val x) (f32val y) then y
  else if PrimFloat.ltb (f32val y) (f32val x) then x
  else if PrimFloat.eqb (f32val x) 0
       then (if PrimFloat.ltb (PrimFloat.div 1 (f32val x)) 0 then y else x)   (* max wants +0 *)
       else x.

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

(** [with_defer cleanup m]: run [m], then run [cleanup] EXACTLY ONCE regardless
    of outcome (Go runs one deferred call once).  If [cleanup] panics, its panic
    replaces any in-flight panic.

    Subtlety (review #6 P0 #1): the cleanup must NOT live inside the [catch] that
    distinguishes the body outcome.  The earlier shape
      [catch (m ;; cleanup ;; ret x) (fun v => cleanup ;; panic v)]
    ran cleanup TWICE when [m] returned normally and cleanup itself panicked: the
    first (in-body) cleanup-panic was caught, and the handler re-ran cleanup.  We
    instead reify [m]'s outcome into a [GoAny + A] sum WITHOUT running cleanup,
    then invoke cleanup exactly once on the single post-[catch] path and re-raise
    the captured body panic afterward. *)
Definition with_defer {A : Type} (cleanup : IO unit) (m : IO A) : IO A :=
  r <-' catch (x <-' m ;; ret (@inr GoAny A x)) (fun v => ret (@inl GoAny A v)) ;;
  cleanup >>' match r with
              | inl v => panic v
              | inr x => ret x
              end.

(** The semantics claimed above, now proven rather than asserted: when the
    guarded body panics, the deferred [cleanup] still runs and the original
    panic propagates afterwards.  Follows from [bind_panic_l] (panic
    short-circuits the body, reifying nothing) and [catch_panic] (the handler
    captures the panic as [inl v]); cleanup then runs once and re-raises it. *)
Lemma with_defer_panic : forall {A} (cleanup : IO unit) (v : GoAny),
  @with_defer A cleanup (panic v) = cleanup >>' panic v.
Proof.
  intros A cleanup v. unfold with_defer.
  rewrite bind_panic_l, catch_panic, bind_ret_l. reflexivity.
Qed.

(** Companion lemma for the NORMAL path, and the regression that pins review #6
    P0 #1: when the body returns [x], cleanup runs and [x] propagates.  Crucially
    this holds UNCONDITIONALLY in [cleanup] — even a [cleanup] that panics is run
    exactly once (the RHS mentions [cleanup] once).  Under the earlier definition
    this equation was FALSE for a panicking cleanup (it ran twice), so this lemma
    could not have been proved; together with [with_defer_panic] it certifies a
    single cleanup execution on both exits. *)
Lemma with_defer_ret : forall {A} (cleanup : IO unit) (x : A),
  @with_defer A cleanup (ret x) = cleanup >>' ret x.
Proof.
  intros A cleanup x. unfold with_defer.
  rewrite bind_ret_l, catch_ret, bind_ret_l. reflexivity.
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

(** ---- Type switch ----  (Go spec: "Type switches")

    Go's [switch v := x.(type) { case T1: …; case T2: …; default: … }] dispatches on
    the RUNTIME type of an interface value [x].  We model it on the SAME [tag_coerce]
    machinery as [type_assert_safe] (so it is axiom-free): try each case's tag against
    the value's tag; the first match runs that case's continuation with the recovered,
    correctly-typed value, otherwise the default runs.  Lowers to Go's native type
    switch.  N-ary (>2 cases) is the same shape with more arms. *)
Definition type_switch2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None => d
          end
      end
  end.

(** Build-checked dispatch: a value tagged [t1] runs the first arm with the recovered
    value (never a wrong arm or the default)… *)
Example type_switch2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k1 : A1 -> IO B) k2 d,
  type_switch2 (anyt t1 x) t1 k1 t2 k2 d = k1 x.
Proof. intros. unfold type_switch2. rewrite tag_coerce_refl. reflexivity. Qed.

(** …and a value whose type matches NEITHER case falls through to the default — the
    coercions are both [None], so no arm can fire on a type mismatch. *)
Example type_switch2_default : forall {B} (x : int) k1 k2 (d : IO B),
  type_switch2 (anyt TInt64 x) TBool k1 TString k2 d = d.
Proof. intros. reflexivity. Qed.

(** N-ary type switch is the same shape with more arms — here three cases.  (The plugin
    lowers any arity through one generalised arm, so [type_switch4]… would work the same.) *)
Definition type_switch3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (k1 : A1 -> IO B)
  (t2 : GoTypeTag A2) (k2 : A2 -> IO B)
  (t3 : GoTypeTag A3) (k3 : A3 -> IO B)
  (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some v1 => k1 v1
      | None =>
          match tag_coerce t2 atag x with
          | Some v2 => k2 v2
          | None =>
              match tag_coerce t3 atag x with
              | Some v3 => k3 v3
              | None => d
              end
          end
      end
  end.

(** Build-checked: the THIRD case fires for an [int64]-tagged value — the first two
    coercions miss (different tags), the third matches and runs [k3] with the value. *)
Example type_switch3_third : forall {B} (x : GoI64) k1 k2 (k3 : GoI64 -> IO B) d,
  type_switch3 (anyt TI64 x) TBool k1 TString k2 TI64 k3 d = k3 x.
Proof. intros. unfold type_switch3. rewrite tag_coerce_refl. reflexivity. Qed.

(** Multi-type case — Go's [case T1, T2:].  A single case matching EITHER of two types;
    in Go the bound value is NOT narrowed (it keeps the interface type), so the body
    commonly ignores it — we model it as a thunk [k : IO B] (no value binder), run when
    the value's type is [t1] OR [t2].  Same [tag_coerce] basis (axiom-free); lowers to
    Go's [case T1, T2:]. *)
Definition type_switch_or2 {A1 A2 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with Some _ => k | None => d end
      end
  end.

(** Build-checked: the multi-type case fires for EITHER tag (here the first and the
    second), and a value matching neither falls through to the default. *)
Example type_switch_or2_first : forall {A1 A2 B} (t1 : GoTypeTag A1) (t2 : GoTypeTag A2)
    (x : A1) (k d : IO B), type_switch_or2 (anyt t1 x) t1 t2 k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_second : forall {B} (x : GoString) (k d : IO B),
  type_switch_or2 (anyt TString x) TBool TString k d = k.
Proof. intros. unfold type_switch_or2. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or2_default : forall {B} (x : int) (k d : IO B),
  type_switch_or2 (anyt TInt64 x) TBool TString k d = d.
Proof. intros. reflexivity. Qed.

(** N-type multi-case — three types here (Go's [case T1, T2, T3:]); same shape as
    [type_switch_or2], one more tag.  The plugin lowers any arity through one generalised
    arm. *)
Definition type_switch_or3 {A1 A2 A3 B : Type} (a : GoAny)
  (t1 : GoTypeTag A1) (t2 : GoTypeTag A2) (t3 : GoTypeTag A3) (k : IO B) (d : IO B) : IO B :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce t1 atag x with
      | Some _ => k
      | None => match tag_coerce t2 atag x with
                | Some _ => k
                | None => match tag_coerce t3 atag x with Some _ => k | None => d end
                end
      end
  end.
Example type_switch_or3_third : forall {B} (x : GoI64) (k d : IO B),
  type_switch_or3 (anyt TI64 x) TBool TString TI64 k d = k.
Proof. intros. unfold type_switch_or3. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_switch_or3_default : forall {B} (x : int) (k d : IO B),
  type_switch_or3 (anyt TInt64 x) TBool TString TFloat64 k d = d.
Proof. intros. reflexivity. Qed.

(** Native EXPRESSION switch — Go's [switch x { case v1: …; case v2: …; default: … }]
    on an int64 scrutinee.  Semantically an equality if-chain (faithful: Go's expression
    switch compares the scrutinee to each case value with [==], first match wins) but
    lowered to the native Go [switch].  Axiom-free (built on [i64_eqb]); N-ary is the same
    shape (the plugin arm is generalised over the (value, body) pairs). *)
Definition int_switch2 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else d.

(** Build-checked dispatch: the scrutinee selects the first matching case, else default. *)
Example int_switch2_first : forall {B} (k1 k2 d : IO B),
  int_switch2 (1)%i64 (1)%i64 k1 (2)%i64 k2 d = k1.
Proof. reflexivity. Qed.
Example int_switch2_second : forall {B} (k1 k2 d : IO B),
  int_switch2 (2)%i64 (1)%i64 k1 (2)%i64 k2 d = k2.
Proof. reflexivity. Qed.
Example int_switch2_default : forall {B} (k1 k2 d : IO B),
  int_switch2 (9)%i64 (1)%i64 k1 (2)%i64 k2 d = d.
Proof. reflexivity. Qed.

(** N-ary expression switch — three cases here; same generalised plugin arm as
    [int_switch2] (it takes any number of (value, body) pairs). *)
Definition int_switch3 {B : Type} (x : GoI64)
  (v1 : GoI64) (k1 : IO B)
  (v2 : GoI64) (k2 : IO B)
  (v3 : GoI64) (k3 : IO B)
  (d : IO B) : IO B :=
  if i64_eqb x v1 then k1
  else if i64_eqb x v2 then k2
  else if i64_eqb x v3 then k3
  else d.
Example int_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (3)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 d = k3.
Proof. reflexivity. Qed.
Example int_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  int_switch3 (9)%i64 (1)%i64 k1 (2)%i64 k2 (3)%i64 k3 d = d.
Proof. reflexivity. Qed.

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
                                   then Some (0%uint63, existT _ K (kt, existT _ V (vt, fun _ => None)))
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
  | Some (_, existT _ _ (kt', existT _ _ (vt', f))) =>
      match tag_eq kt kt', tag_eq vt vt' with
      | Some pk, Some pv =>
          fun k => eq_rect _ (fun Y : Type => option Y)
                           (f (eq_rect _ (fun X : Type => X) k _ pk)) _ (eq_sym pv)
      | _, _ => fun _ => None
      end
  | None => fun _ => None
  end.
Definition map_write {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                      (m : GoMap K V) (f : K -> option V) (sz : int) (w : World) : World :=
  mkWorld (w_refs w) (w_chans w)
          (fun l => if PrimInt63.eqb l (gm_loc m)
                    then Some (sz, existT _ K (kt, existT _ V (vt, f)))
                    else w_maps w l)
          (w_next w).
Definition map_sel {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : option V :=
  map_get_fn kt vt m w k.
(** [map_size] = Go's [len(m)]: the live-key count stored in the map's cell (0 if the map has no cell yet
    / is nil).  The plugin lowers [map_len] by name to Go [len(m)]; this model now AGREES with it. *)
Definition map_size {K V} (m : GoMap K V) (w : World) : GoInt :=
  match w_maps w (gm_loc m) with Some (sz, _) => sz | None => 0%uint63 end.
Definition map_upd {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (v : V) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then Some v else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len UNCHANGED on an existing key; +1 on a new one *)
     | Some _ => map_size m w | None => PrimInt63.add (map_size m w) 1%uint63 end) w.
Definition map_rem {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
                   (k : K) (m : GoMap K V) (w : World) : World :=
  map_write kt vt m (fun k' => if key_eqb kt k k' then None else map_get_fn kt vt m w k')
    (match map_get_fn kt vt m w k with         (* len −1 on a present key; UNCHANGED if absent *)
     | Some _ => PrimInt63.sub (map_size m w) 1%uint63 | None => map_size m w end) w.

(** Read-back-after-write: [map_get_fn] of a [map_write] (with the SAME tags) is
    the written function — via [eqb_refl] (location hit) + [tag_eq_refl] (the K/V
    coercions become identities, then eta). *)
Lemma map_get_fn_write_same : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) m f sz w,
  map_get_fn kt vt m (map_write kt vt m f sz w) = f.
Proof.
  intros K V kt vt m f sz w. unfold map_get_fn, map_write. cbn.
  rewrite (Uint63.eqb_refl (gm_loc m)), !tag_eq_refl. reflexivity.
Qed.

(** Break #2 witness (machine-checked): [map_size] now reports the REAL live-key count = Go's [len(m)].
    Insert keys 1,2; overwrite key 1 (len stays 2); delete key 2 (len → 1). *)
Example map_len_counts :
  match run_io (map_make_typed TI64 TI64)
               (mkWorld (fun _ => None) (fun _ => None) (fun _ => None) 1%uint63) with
  | ORet m w1 =>
      let w2 := map_upd TI64 TI64 (i64wrap 1%Z) (i64wrap 10%Z) m w1 in
      let w3 := map_upd TI64 TI64 (i64wrap 2%Z) (i64wrap 20%Z) m w2 in
      let w4 := map_upd TI64 TI64 (i64wrap 1%Z) (i64wrap 99%Z) m w3 in  (* overwrite key 1 — len stays 2 *)
      let w5 := map_rem TI64 TI64 (i64wrap 2%Z) m w4 in                 (* delete key 2 — len → 1 *)
      andb (PrimInt63.eqb (map_size m w4) 2%uint63)
           (PrimInt63.eqb (map_size m w5) 1%uint63) = true
  | OPanic _ _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

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
(** Break #6 (maps): a WRITE to a NIL map ([MkMap 0], [gm_loc = 0]) PANICS — Go's "assignment to entry
    in nil map" — instead of fabricating a cell at the reserved location 0.  (Go's nil map is fine to
    READ — zero for every key — and to [delete]/[clear] — no-ops; only assignment panics, so only
    [map_set] gains the guard.)  Location 0 is reserved by [ValidWorld] (break #5), so [eqb (gm_loc m) 0]
    exactly detects nil.  Lowered by name ([m[k] = v]), so the guard is golden-stable. *)
Definition map_set {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) : IO unit :=
  fun w => if PrimInt63.eqb (gm_loc m) 0%uint63 then OPanic (any tt) w
           else ORet tt (map_upd kt vt k v m w).
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
  run_io (map_set kt vt k v m) w =
    if PrimInt63.eqb (gm_loc m) 0%uint63 then OPanic (any tt) w
    else ORet tt (map_upd kt vt k v m w).
Proof. reflexivity. Qed.

(** Faithfulness: assigning to a NIL map PANICS, exactly as Go's [m[k] = v] on a nil [m]. *)
Lemma map_set_nil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World),
  run_io (map_set kt vt k v (@map_empty K V)) w = OPanic (any tt) w.
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
(** DELETE FRAME (the dual of [map_sel_rem], mirroring [map_sel_upd_diff] for set): deleting key [k2]
    leaves a DIFFERENT key [k1] reading exactly what it read before — Go's `delete(m, k2)` touches only
    [k2].  Independence of keys is as defining for a map as [map_sel_rem] is. *)
Theorem map_sel_rem_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 ->
  map_sel kt vt k1 m (map_rem kt vt k2 m w) = map_sel kt vt k1 m w.
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne. unfold map_sel, map_rem.
  rewrite map_get_fn_write_same. cbn.
  destruct (key_eqb kt k2 k1) eqn:E.
  - exfalso. apply Hne. symmetry. apply Hcmp. exact E.
  - reflexivity.
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
  rewrite !run_bind, !run_map_set.
  destruct (PrimInt63.eqb (gm_loc m) 0%uint63) eqn:Hnil.
  - reflexivity.   (* nil map: both sides panic at the [map_set] step *)
  - cbn. rewrite run_map_get_opt, map_sel_upd_same by (apply comparable_key_refl; exact Hcmp).
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

(** Setting key [k2] leaves the read at a different key [k1] unchanged — on a NON-NIL map (a nil map
    would panic at the [map_set], so the post-state is not [map_upd]). *)
Lemma map_get_set_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (v : V) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 -> PrimInt63.eqb (gm_loc m) 0%uint63 = false ->
  run_io (bind (map_set kt vt k2 v m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_upd kt vt k2 v m w).
Proof.
  intros K V kt vt k1 k2 v m w Hcmp Hne Hnil.
  rewrite run_bind, run_map_set, Hnil. cbn.
  rewrite run_map_get_opt, map_sel_upd_diff by assumption. reflexivity.
Qed.

(** IO-level delete frame (the comma-ok dual of [map_get_set_diff]): after `delete(m, k2)`, the
    two-value lookup of a DIFFERENT key [k1] returns exactly what it returned before the delete. *)
Lemma map_get_delete_diff : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V)
    (k1 k2 : K) (m : GoMap K V) (w : World),
  Comparable kt -> k1 <> k2 ->
  run_io (bind (map_delete kt vt k2 m) (fun _ => map_get_opt kt vt k1 m)) w =
  ORet (map_sel kt vt k1 m w) (map_rem kt vt k2 m w).
Proof.
  intros K V kt vt k1 k2 m w Hcmp Hne.
  rewrite run_bind, run_map_delete. cbn.
  rewrite run_map_get_opt, map_sel_rem_diff by assumption. reflexivity.
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
  map_write kt vt m (fun _ => None) 0%uint63 w.   (* clear ⇒ empty ⇒ len 0 *)
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
(** Break #6 (channels): [close] on a NIL channel ([MkChan 0]) PANICS — Go's "close of nil channel" —
    instead of fabricating a close at the reserved location 0.  (Go also panics on a double-close, the
    [chan_closed] guard below.)  [send]/[recv] on a nil channel BLOCK FOREVER in Go; that is the documented
    "blocking idealised away" limitation (a faithful model needs a divergence/stuck outcome — foundation),
    and like all nil ops it is UNREACHABLE in the closed world ([make_chan] mints a nonzero handle —
    [chan_alloc_close_no_panic]).  Lowered by name ([close(ch)]), so the guard is golden-stable. *)
Definition close_chan {A} (tag : GoTypeTag A) (ch : GoChan A) : IO unit :=
  fun w => if PrimInt63.eqb (ch_loc ch) 0%uint63 then OPanic (any tt) w
           else if chan_closed ch w then OPanic (any tt) w else ORet tt (chan_close_upd tag ch w).
Definition recv_ok {A B} (tag : GoTypeTag A) (ch : GoChan A) (f : A -> bool -> IO B) : IO B :=
  fun w => match chan_buf tag ch w with
           | v :: _ => f v true (chan_recv_upd tag ch w)
           | nil    => f (zero_val tag) false w
           end.
Definition select_recv2 {A B C} (ta : GoTypeTag A) (ch1 : GoChan A) (k1 : A -> IO C)
                                 (tb : GoTypeTag B) (ch2 : GoChan B) (k2 : B -> IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then k1 (zero_val ta) w   (* ch1 CLOSED+drained: recv READY, yields zero (Go) *)
                       else match chan_buf tb ch2 w with
                            | v :: _ => k2 v (chan_recv_upd tb ch2 w)
                            | nil    => if chan_closed ch2 w then k2 (zero_val tb) w  (* ch2 closed+drained: zero *)
                                        else k1 (zero_val ta) w        (* both empty+OPEN: fabricated zero — Go BLOCKS (documented unsoundness) *)
                            end
           end.
(** [select_recv_default] — recv case + [default].  A CLOSED, DRAINED channel's recv is READY in
    Go (yields the zero value immediately), so [default] is taken ONLY when the channel is empty
    AND OPEN (code-review fix 2026-06-20 — examining only the buffer mispredicted [default] for a
    closed channel). *)
Definition select_recv_default {A C} (ta : GoTypeTag A) (ch1 : GoChan A)
                                      (k1 : A -> IO C) (d : IO C) : IO C :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => k1 v (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then k1 (zero_val ta) w   (* closed+drained: recv READY, zero *)
                       else d w                                        (* open+empty: default *)
           end.
(** CORRECTNESS — closed-channel readiness (code-review example): on a CLOSED, DRAINED channel the
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

(** ── Toward a UNIFIED control-flow substrate: select as SENTINEL + goto (2026-06-19) ──
    [select] factors into a runtime WAIT that returns WHICH case fired plus a pure CFG DISPATCH
    (goto) on that index — no bespoke select control-flow node is needed in the substrate.
    [select_wait2] is the SENTINEL; [select2] is the canonical DESUGAR ([bind select_wait2] then a
    [match] (goto) on the index).  *Next: teach the relooper to LIFT the [select_wait2] sentinel +
    dispatch back to Go [select{}] (error otherwise), making the goto-CFG the single static-
    control-flow substrate; [select2] is the only producer of the sentinel, so the lifted shape is
    a valid select by construction — strictness in Rocq, not the trusted relooper.*

    ⚠ SCOPE OF THE THEOREM (code reviews, 2026-06-19/20 — corrects an earlier overclaim, sharpened
    by a follow-up review).  This [select_wait2] inherits the [select_recv2] model's behaviour, a
    DETERMINISTIC UNDER-APPROXIMATION of Go's select, so [select2_eq_recv2] proves the desugar equals
    that *idealised model*, NOT equivalence to Go.  Two distinct unsoundnesses:
      (1) CHOICE: both channels ready ⇒ it deterministically takes ch1; Go picks pseudo-randomly among
          ready cases.  Counterexample: both ready, [k1 ↦ 1], [k2 ↦ 2] — Rocq always 1, Go may return
          2.  So native Go does NOT *refine* this deterministic function (Go exhibits "take ch2", a
          behaviour the function FORBIDS) — the function is at best ONE example scheduler / an
          executable test interpreter, NON-AUTHORITATIVE as a spec.  The authoritative spec is
          relational/nondeterministic, and a safety property must hold for EVERY permitted choice,
          not just ch1.
      (2) BLOCKING: none ready and no default ⇒ it returns the fabricated [(0, zero)]; Go BLOCKS.  But
          blocking is NOT divergence: in a concurrent program this goroutine merely has NO TRANSITION
          right now while *other* goroutines may still step — it is DEADLOCK only when the WHOLE
          program cannot step.  [concurrency.v] already models exactly this (a goroutine like
          [block_cfg]'s [PRecv 0] with no sender has no [step]; [Stuck := ~ can_step /\ ~ done] is the
          GLOBAL deadlock property).  So empty-select is a LOCAL non-step — never a fabricated value,
          never collapsed into permanent nontermination.
    The EXTRACTION is faithful (native Go [select{}]); it is the MODEL that licenses unsound *proofs*
    about correct Go.  The robust fix belongs in the [rstep] calculus, NOT this sequential [IO] model:
    a NONDETERMINISTIC/relational [select_wait] ranging over every ready case, the lift quantified over
    the chosen index ([rstep] is exactly this shape).  A sound-but-narrow interim — demand a proof that
    EXACTLY ONE case is ready (then determinism = Go) — is sound ONLY under an interference-freedom /
    ownership discipline keeping that readiness STABLE until the selection point; otherwise another
    goroutine can change readiness between the proof and the native select (a TOCTOU gap).  Tracked in
    Known gaps / SPEC_CONFORMANCE.

    THIRD REVIEW (2026-06-20) — one FIX (below) + two items SINCE RESOLVED in [concurrency.v]:
    • FIXED here: a CLOSED, DRAINED channel's recv is READY in Go (yields zero immediately), but the
      sequential model examined only the buffer and mispredicted [default] / fabricated the other case.
      [select_recv_default]/[select_recv2]/[select_wait2] now check [chan_closed]: empty+closed ⇒ that
      recv case fires with the zero value; [default] only on empty+OPEN.  Witnessed by
      [select_default_closed] / [select_default_open_empty]; [select2_eq_recv2] re-proven.
    • RESOLVED (relational closed): the relational select now MODELS closed channels — closed-state is
      read off the TRACE ([closedb]: some [KClose c] event), so there is no config flag and no
      backpointer gap (the [KClose] position itself IS the closed-recv's happens-before producer).
      [rstep_recv_closed] / [rstep_select_closed] step a closed-drained recv/select to the zero value;
      [closed_select_can_step] / [rclosed_select_can_step] witness it; [closed_recv_preserves_inv]
      keeps the resulting trace well-formed.
    • RESOLVED (rich calculus + typed connection): the value-carrying [rstep]/[Cmd] calculus now has a
      first-class [CSelect] with PER-CASE channel + continuation — [select { case <-ch: A() | case <-ch:
      B() }] (same channel, distinct bodies) is representable and the two successors run DIFFERENT bodies
      ([rselect_per_case_continuation]).  The typed↔relational bridge is proven: [det_select_sound] (the
      deterministic ch1-priority pick is always a permitted [rstep_select]); [det_select_incomplete] (two
      ready ⇒ it MISSES the other successor); [det_select_complete_unique] / [det_select_exact_unique] (a
      UNIQUE ready case ⇒ it is also COMPLETE — the exact converse, so the deterministic model is fully
      faithful precisely in the unique-ready regime); and [select_fire_is_recv_fire] (firing a ready case
      reaches the same config as a plain recv, mirroring [select_recv2_ch1_buffered] here).
    GENUINE remainder: a SINGLE composed theorem carrying a [select_recv2] World execution all the way to
    a permitted [rstep_select] (today [select_recv2] = [recv] (World) ∘ [denote_sim_recv] ∘
    [select_fire_is_recv_fire] is argued in prose, not yet ONE lemma); and full [rstep] determinism in the
    CLOSED regime additionally needs close-position uniqueness (a [WfTrace] strengthening — at most one
    [KClose] per channel).  Until those, the typed [select] is SOUND, with completeness pinned to the
    unique-ready regime above. *)
Definition select_wait2 {A} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) : IO (nat * A) :=
  fun w => match chan_buf ta ch1 w with
           | v :: _ => ORet (0, v) (chan_recv_upd ta ch1 w)
           | nil    => if chan_closed ch1 w then ORet (0, zero_val ta) w   (* ch1 closed+drained: case 0 fires, zero *)
                       else match chan_buf ta ch2 w with
                            | v :: _ => ORet (1, v) (chan_recv_upd ta ch2 w)
                            | nil    => if chan_closed ch2 w then ORet (1, zero_val ta) w  (* ch2 closed+drained: case 1, zero *)
                                        else ORet (0, zero_val ta) w
                            end
           end.
Definition select2 {A C} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) (k1 k2 : A -> IO C) : IO C :=
  bind (select_wait2 ta ch1 ch2)
       (fun iv => match fst iv with O => k1 (snd iv) | _ => k2 (snd iv) end).

(** The desugar is faithful TO THE IDEALISED MODEL: select-via-(wait + index-goto) IS the current
    [select_recv2].  (NOT equivalence to Go — see the ⚠ scope note above: the model is a
    deterministic, blocking-idealised under-approximation of Go's nondeterministic select.) *)
Theorem select2_eq_recv2 :
  forall {A C} (ta : GoTypeTag A) (ch1 ch2 : GoChan A) (k1 k2 : A -> IO C),
    select2 ta ch1 ch2 k1 k2 = select_recv2 ta ch1 k1 ta ch2 k2.
Proof.
  intros A C ta ch1 ch2 k1 k2. apply run_io_inj. intro w.
  unfold select2, select_recv2, select_wait2, bind, run_io.
  destruct (chan_buf ta ch1 w) as [|v1 r1].
  - destruct (chan_closed ch1 w).
    + reflexivity.                                    (* ch1 closed+drained: both → k1 zero *)
    + destruct (chan_buf ta ch2 w) as [|v2 r2].
      * destruct (chan_closed ch2 w); reflexivity.    (* ch2 closed → k2 zero; else fabricated k1 zero *)
      * reflexivity.                                  (* ch2 ready *)
  - reflexivity.                                      (* ch1 ready *)
Qed.

(** ── WORLD-level select↔recv bridge.  Go: "if one or more of the communications can proceed, a
    single one ... is chosen."  When the ch1-priority [select_recv2]'s FIRST channel is READY
    (buffered, or closed-and-drained), it behaves EXACTLY like a plain [recv] on that channel —
    [run_io]-equal to [bind (recv ta ch1) k1].  So a ready case makes select reduce to a recv on the
    chosen channel, and select INHERITS [recv]'s [run_io] laws and operational refinement
    ([denote_sim_recv] / [rstep_recv]); the calculus-level [det_select_sound] (concurrency.v) used
    [sel_first_ready] as a STAND-IN for [select_recv2] — these connect the real [select_recv2] to
    [run_io] directly.  Faithful for the cases that CAN proceed (Go's "communication can proceed");
    the both-empty-open fall-through stays the documented blocking-idealisation. *)

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
  PrimInt63.eqb (ch_loc ch) 0%uint63 = false ->
  chan_closed ch w = false ->
  run_io (close_chan tag ch) w = ORet tt (chan_close_upd tag ch w).
Proof. intros A tag ch w Hnn H. unfold close_chan, run_io. rewrite Hnn, H. reflexivity. Qed.
Lemma run_close_closed : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  chan_closed ch w = true ->
  run_io (close_chan tag ch) w = OPanic (any tt) w.
Proof.
  intros A tag ch w H. unfold close_chan, run_io. rewrite H.
  destruct (PrimInt63.eqb (ch_loc ch) 0%uint63); reflexivity.   (* nil OR closed ⇒ panic *)
Qed.
(** Faithfulness: [close] on a nil channel PANICS, exactly as Go's [close(nil)]. *)
Lemma close_chan_nil : forall {A} (tag : GoTypeTag A) (w : World),
  run_io (close_chan tag (@MkChan A 0%uint63)) w = OPanic (any tt) w.
Proof. reflexivity. Qed.

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

(** Sending on a closed channel panics (Go spec): close then send → panic.  (On a non-nil channel — a
    nil one would panic at the first [close].) *)
Theorem send_closed_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (w : World),
  PrimInt63.eqb (ch_loc ch) 0%uint63 = false ->
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => send tag ch v)) w
  = OPanic (any tt) (chan_close_upd tag ch w).
Proof.
  intros A tag ch v w Hnn Hopen.
  rewrite run_bind, (run_close tag ch w Hnn Hopen). cbn.
  exact (run_send_closed tag ch v (chan_close_upd tag ch w) (chan_closed_close tag ch w)).
Qed.

(** Closing an already-closed channel panics (Go spec): close then close → panic.  (On a non-nil
    channel — a nil one would panic at the first [close].) *)
Theorem double_close_panics : forall {A} (tag : GoTypeTag A) (ch : GoChan A) (w : World),
  PrimInt63.eqb (ch_loc ch) 0%uint63 = false ->
  chan_closed ch w = false ->
  run_io (bind (close_chan tag ch) (fun _ => close_chan tag ch)) w
  = OPanic (any tt) (chan_close_upd tag ch w).
Proof.
  intros A tag ch w Hnn Hopen.
  rewrite run_bind, (run_close tag ch w Hnn Hopen). cbn.
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
(* review R5: [cap] on a functional (value) [GoSlice] is NOT Go's capacity.  Go's [cap] after [append]
   is IMPLEMENTATION-DEFINED (append may over-allocate), so no value-slice model can predict it; this
   [cap = len] is a proof-only convenience and is NOT extractable — the plugin emits [unsupported] for
   any [cap] use (a value that [go build] would accept but that is WRONG at runtime).  Capacity-aware
   code uses the heap-backed [SliceH], whose capacity ([sh_cap]) is an explicit field of the value. *)
Definition cap {A} (xs : GoSlice A) : GoInt := len xs.   (* proof-only; NOT Go's cap — see R5 note above *)
Definition append {A} (xs ys : GoSlice A) : GoSlice A := xs ++ ys.   (* GoSlice A = list A *)

(** [min]/[max] (Go 1.21 predeclared builtins) on [int] — the smaller / larger of
    two values, by the SIGNED ordering (Go's int [<]), so [go_min] = Go [min(a,b)]
    and [go_max] = Go [max(a,b)] for the [int] type.  Computable (so [go_min 3 5 =
    3] is a THEOREM); the plugin lowers the call to Go's builtin.  (Go's [min]/[max]
    also apply to floats — with NaN/`-0` corner cases — and strings; those follow
    once those orderings are settled.) *)
Definition go_min (a b : int) : int := if Sint63.ltb a b then a else b.
Definition go_max (a b : int) : int := if Sint63.ltb a b then b else a.

(** [min]/[max] on the CANONICAL full-width types: [int64] ([GoI64], SIGNED order via
    [i64_ltb]) and [uint64] ([GoU64], UNSIGNED order via [u64_ltb]) — each exactly Go's
    [min(a,b)]/[max(a,b)] for that type.  Computable theorems; the plugin lowers each
    call to the Go builtin.  No carrier bridge (the comparison is the type's own [<]). *)
Definition i64_min (a b : GoI64) : GoI64 := if i64_ltb a b then a else b.
Definition i64_max (a b : GoI64) : GoI64 := if i64_ltb a b then b else a.
Definition u64_min (a b : GoU64) : GoU64 := if u64_ltb a b then a else b.
Definition u64_max (a b : GoU64) : GoU64 := if u64_ltb a b then b else a.

(** [min]/[max] on FLOAT (Go spec "min and max" — the float rules).  A naive
    [if a < b] is WRONG on two IEEE corners that Go's builtin handles, so we model
    them faithfully (the body is suppressed; each call lowers to Go's [min]/[max],
    which does the same):
    - NaN PROPAGATION: if either argument is a NaN, the result is a NaN.  Detected by
      [eqb x x = false] (only NaN is unequal to itself).
    - SIGNED ZERO: when the two are numerically EQUAL and are [±0], [max] yields [+0]
      and [min] yields [-0] (Go treats [+0 > -0]).  Detected by [eqb a 0] (both are
      [±0]) and [1/a < 0] (a is the negative zero, since [1 / -0 = -inf]).
    Otherwise the smaller / larger by [ltb].  Machine-checked on all these corners. *)
Definition f64_min (a b : float) : float :=
  if negb (PrimFloat.eqb a a) then a            (* a is NaN → NaN *)
  else if negb (PrimFloat.eqb b b) then b       (* b is NaN → NaN *)
  else if PrimFloat.ltb a b then a
  else if PrimFloat.ltb b a then b
  else (* numerically equal (incl. ±0) *)
    if PrimFloat.eqb a 0
    then (if PrimFloat.ltb (PrimFloat.div 1 a) 0 then a else b)   (* min wants -0 *)
    else a.
Definition f64_max (a b : float) : float :=
  if negb (PrimFloat.eqb a a) then a            (* a is NaN → NaN *)
  else if negb (PrimFloat.eqb b b) then b       (* b is NaN → NaN *)
  else if PrimFloat.ltb a b then b
  else if PrimFloat.ltb b a then a
  else (* numerically equal (incl. ±0) *)
    if PrimFloat.eqb a 0
    then (if PrimFloat.ltb (PrimFloat.div 1 a) 0 then b else a)   (* max wants +0 *)
    else a.

(** Direct [>] / [>=] / [!=] for float64.  CRUCIAL NaN subtlety: [>=] is NOT
    [¬(<)] — with a NaN operand, [a >= b] is FALSE (Go/IEEE), whereas [¬(a < b)]
    would be TRUE.  So [f64_geb] is the SWAPPED [leb] ([b <= a]), and [f64_gtb] the
    swapped [ltb] — both correctly false on NaN.  [f64_neqb] IS [negb (eqb)] (a NaN
    compares UNEQUAL to everything, so [a != b] is true — matching [negb false]). *)
Definition f64_gtb  (a b : float) : bool := PrimFloat.ltb b a.
Definition f64_geb  (a b : float) : bool := PrimFloat.leb b a.
Definition f64_neqb (a b : float) : bool := negb (PrimFloat.eqb a b).

(** Construct a typed Go slice from a Rocq list literal.
    The [GoTypeTag] witness lets the plugin emit [[]T{v1, v2, ...}] with the
    correct element type instead of falling back to [append(nil, ...)]. *)
Definition slice_of_list {A} (_ : GoTypeTag A) (xs : list A) : GoSlice A := xs.

(** Variadic parameter (Go [func f(xs ...T)]): inside [f] the param is a SLICE, but Go's call
    syntax SPREADS — [f(slice...)].  [Variadic T] is a 2-FIELD record (the [bool] phantom stops
    Coq from unboxing the single slice field, so the PARAM TYPE stays distinguishable from a
    plain [[]T] — the plugin renders it [...T], not [[]T]; no [Comparable] is needed for a
    variadic param so the phantom-breaks-equality issue that ruled this out for [GoI64] does
    not apply here).  [vararg xs] marks a call argument for spreading ([xs...]); inside [f],
    [va_slice] recovers the slice (it is the param itself, so it lowers to identity). *)
Record Variadic (T : Type) := MkVariadic { va_slice : GoSlice T ; va_ph : bool }.
Arguments MkVariadic {T} _ _.
Arguments va_slice {T} _.  Arguments va_ph {T} _.
Definition vararg {T} (xs : GoSlice T) : Variadic T := MkVariadic xs true.

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

(** ---- Arrays (Go spec "Array types"): a FIXED-SIZE [N]T VALUE (Phase B4.1) ----
    Go's [N]T carries the size [N] in the TYPE, but Coq extraction ERASES value-level
    type indices, so [N] is unrecoverable from the extracted type.  The way around it
    for LOCAL arrays: keep the size OUT of the Coq type ([GoArray A], size-erased) and
    put it in the CONSTRUCTION — [arr_lit l] lowers to [[len(l)]T{…}] (the size read off
    the list, exactly as [slice_of_list] reads it for [[]T{…}]).  A local [a := arr_lit …]
    then has its Go type INFERRED from the literal, so the plugin never emits a bare
    [[N]T] annotation.  Distinct from a slice: VALUE semantics, fixed length (an
    array-typed param/field/return — needing an explicit [N]T — is refused, fail-loud;
    that is the type-level-[N] route, deferred).  [GoArray A = list A] under the hood,
    but the ops are recognized BY NAME and lower to native array Go. *)
Record GoArray (A : Type) := mkArray { arr_data : list A }.
Arguments mkArray {A} _.  Arguments arr_data {A} _.

Definition arr_lit {A} (_ : GoTypeTag A) (l : list A) : GoArray A := mkArray l.

(** Fixed-size array in a TYPED POSITION (struct field / param / return / typed var) — Go's
    [[N]T], where [N] is part of the TYPE.  [GoArray] above SIZE-ERASES [N] (fine for LOCAL
    arrays where Go infers the size from the literal), but a typed position needs [N] back.  First
    cut: the canonical small size 3 (a 3-vector) as a CONCRETE type [GoArr3], rendered by the
    plugin as [[3]T].  Its constructor takes EXACTLY THREE elements, so the length is 3 BY
    CONSTRUCTION — no proof obligation, and no uncompilable wrong-length literal can arise.
    (Other fixed sizes are their own type; arbitrary type-level [N] is a deferred route.) *)
Record GoArr3 (A : Type) := mkArr3 { arr3_data : list A }.
Arguments mkArr3 {A} _.  Arguments arr3_data {A} _.
Definition arr3_lit {A} (_ : GoTypeTag A) (x y z : A) : GoArr3 A := mkArr3 (x :: y :: z :: nil).
(* Another size — the plugin handles ANY [GoArr<N>] generically (N parsed from the name). *)
Record GoArr2 (A : Type) := mkArr2 { arr2_data : list A }.
Arguments mkArr2 {A} _.  Arguments arr2_data {A} _.
Definition arr2_lit {A} (_ : GoTypeTag A) (x y : A) : GoArr2 A := mkArr2 (x :: y :: nil).

(** Safe indexed read (CPS / comma-ok like [slice_at_ok] — Go arrays panic on OOB too):
    in range ⇒ [k a[i] true], else [k zero false].  The signed guard covers both ends.
    Lowers IDENTICALLY to [slice_at_ok] (array and slice both index [a[i]] with [len(a)]),
    so the plugin reuses that arm. *)
Definition arr_get_ok {A B} (tag : GoTypeTag A) (a : GoArray A) (i : int) (k : A -> bool -> IO B) : IO B :=
  if (Sint63.leb 0 i && Sint63.ltb i (len (arr_data a)))%bool
  then k (go_list_nth (arr_data a) i (zero_val tag)) true
  else k (zero_val tag) false.

(* The construction round-trips: [arr_lit]'s data IS the given list (so [arr_get_ok]
   reads the i'th element placed). *)
Lemma arr_data_lit : forall {A} (tag : GoTypeTag A) (l : list A), arr_data (arr_lit tag l) = l.
Proof. reflexivity. Qed.

(** Array COMPARABILITY (Go spec "Comparison operators": arrays are comparable iff the
    element type is — unlike SLICES, which are NOT comparable).  Go's array [==] is
    FIELD-WISE; [arr_eqb] decides it element-by-element (here for [int64] arrays), so it
    is a THEOREM that it decides array equality.  Lowers to the bare Go [a == b].  Go
    requires the two arrays be the SAME type (same length) for [==] — different lengths
    are a Go COMPILE error, so only same-length arrays are compared. *)
Fixpoint goi64_list_eqb (xs ys : list GoI64) : bool :=
  match xs, ys with
  | nil, nil => true
  | x :: xs', y :: ys' => andb (i64_eqb x y) (goi64_list_eqb xs' ys')
  | _, _ => false
  end.
Definition arr_eqb (a b : GoArray GoI64) : bool := goi64_list_eqb (arr_data a) (arr_data b).
Definition arr3_eqb (a b : GoArr3 GoI64) : bool := goi64_list_eqb (arr3_data a) (arr3_data b).
Definition arr2_eqb (a b : GoArr2 GoI64) : bool := goi64_list_eqb (arr2_data a) (arr2_data b).

(** Array VALUE-COPY (the defining array-vs-slice distinction): [b := arr_set a i v] is
    [a] with element [i] replaced — a FUNCTIONAL update, so [a] is UNCHANGED (value
    semantics; a slice would share the backing).  Lowers to the copy-mutate-return IIFE
    [func(_a [n]T) [n]T { _a[i] = v; return _a }(a)] — Go copies [a] into the value
    parameter, mutates the COPY, and returns it, leaving [a] untouched.  [n] (the size,
    erased from the Coq type) is passed explicitly (the author knows it — the
    size-in-construction principle), so the plugin can emit the [n]T] annotation. *)
Fixpoint go_list_set {A} (xs : list A) (i : int) (v : A) : list A :=
  match xs with
  | nil => nil
  | x :: xs' => if PrimInt63.eqb i 0%uint63 then v :: xs'
                else x :: go_list_set xs' (PrimInt63.sub i 1%uint63) v
  end.
Definition arr_set {A} (_n : nat) (_ : GoTypeTag A) (a : GoArray A) (i : int) (v : A) : GoArray A :=
  mkArray (go_list_set (arr_data a) i v).

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
      u8wrap (PrimInt63.add (v b0 1%uint63)
           (PrimInt63.add (v b1 2%uint63)
           (PrimInt63.add (v b2 4%uint63)
           (PrimInt63.add (v b3 8%uint63)
           (PrimInt63.add (v b4 16%uint63)
           (PrimInt63.add (v b5 32%uint63)
           (PrimInt63.add (v b6 64%uint63) (v b7 128%uint63))))))))
  end.
Fixpoint go_str_byte (s : GoString) (i : int) : GoByte :=
  match s with
  | EmptyString  => u8wrap 0
  | String c rest => if PrimInt63.eqb i 0%uint63 then ascii_byte c
                     else go_str_byte rest (PrimInt63.sub i 1%uint63)
  end.

(** ---- [[]byte] / [string] conversions (Go spec "Conversions to and from a string
    type") ----  [[]byte(s)] is the BYTE sequence of [s] (no UTF-8 decoding); [string(b)]
    reconstructs it.  [GoString] IS a byte sequence ([list ascii]), so these are faithful
    byte-for-byte.  [str_to_bytes] maps each char to its [GoByte] via the suppressed
    [ascii_byte]; [byte_ascii] is its inverse (reconstruct the 8 bits, again no
    [nat_of_ascii]).  Both lower BY NAME to the native [[]byte(s)] / [string(b)] (bodies
    suppressed + NoInline, so they affect only proofs).  [str_to_bytes_length] proves the
    byte count is preserved ([len([]byte(s)) == len(s)]); the value round-trip is golden. *)
Definition byte_ascii (b : GoByte) : ascii :=
  let n := u8raw b in
  let bit (k : int) : bool := PrimInt63.eqb (PrimInt63.land (PrimInt63.lsr n k) 1%uint63) 1%uint63 in
  Ascii (bit 0%uint63) (bit 1%uint63) (bit 2%uint63) (bit 3%uint63)
        (bit 4%uint63) (bit 5%uint63) (bit 6%uint63) (bit 7%uint63).
Fixpoint str_to_bytes (s : GoString) : list GoByte :=
  match s with
  | EmptyString   => nil
  | String c rest => ascii_byte c :: str_to_bytes rest
  end.
Fixpoint str_from_bytes (b : list GoByte) : GoString :=
  match b with
  | nil       => EmptyString
  | x :: rest => String (byte_ascii x) (str_from_bytes rest)
  end.
Lemma str_to_bytes_length : forall s, Datatypes.length (str_to_bytes s) = String.length s.
Proof. induction s as [|c rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Definition str_at_ok {B : Type}
  (s : GoString) (i : int) (k : GoByte -> bool -> IO B) : IO B :=
  if (Sint63.leb 0 i && Sint63.ltb i (str_len s))%bool
  then k (go_str_byte s i) true
  else k (u8wrap 0) false.

Fixpoint str_concat (a b : GoString) : GoString :=
  match a with
  | EmptyString   => b
  | String c rest => String c (str_concat rest b)
  end.

(** String slicing [s[a:b]] (Go spec "Slice expressions": for a string, the result is the
    BYTE-substring [a, b)).  EVIDENCE-CARRYING / safe-by-construction: it DEMANDS a proof
    that [a <= b <= len(s)] (in bytes), so the emitted [s[a:b]] cannot panic — the bounds
    proof discharged Go's slice-bounds check (same discipline as [div_nz]).  Indices are
    [nat] (a string length/offset is non-negative; this also keeps the body conversion-free
    — no [Sint63.to_Z] to bridge).  The body [String.substring a (b-a) s] is recognized
    away to the native [s[a:b]] (decl + [substring] suppressed).  [eq_refl] discharges the
    proof for literal bounds. *)
Definition str_slice (s : GoString) (a b : nat)
  (_ : (Nat.leb a b && Nat.leb b (String.length s))%bool = true) : GoString :=
  String.substring a (b - a) s.

(** ---- Rune view: [[]rune(s)] / [string([]rune)] (Go spec "Conversions to and from a
    string type") ----  A [rune] is an int32 code point.  [[]rune(s)] UTF-8-DECODES the
    byte sequence to code points; [string(rs)] UTF-8-ENCODES them back.  Both lower BY NAME
    to the native Go [[]rune(s)] / [string(rs)] (the runtime does the real UTF-8, faithful);
    the Coq bodies below are the proof-side model (suppressed + NoInline), a full 1–4 byte
    UTF-8 codec.  [byte_chr] is a byte value → [ascii]; the codec is verified by the
    round-trip examples (ASCII and a 3-byte CJK code point). *)
Definition byte_chr (v : int) : ascii := byte_ascii (u8wrap v).

(** Break #10: [str_to_runes] is now a FAITHFUL UTF-8 decoder — exactly Go's [utf8.DecodeRune] /
    range-over-string.  An invalid sequence yields [RuneError] (U+FFFD) and advances by exactly ONE byte
    (NOT the would-be width), rejecting: continuation bytes used as leads (0x80–0xBF), overlong 2-byte
    (0xC0/0xC1), missing/bad continuation bytes, overlong 3/4-byte (0xE0 with c1<0xA0; 0xF0 with c1<0x90),
    UTF-16 surrogates (0xED with c1≥0xA0), >MaxRune (0xF4 with c1≥0x90), and invalid leads ≥0xF5.  The body
    is proof-only (lowered by name to native [[]rune(s)], which does the same), so this only corrects the
    MODEL to match Go; golden is unaffected. *)
(** [str_to_runes_w] decodes AND records, per rune, the number of SOURCE bytes consumed (1 for an
    invalid byte — Go's [utf8.DecodeRune] advances exactly one — or the 2/3/4 of a valid multibyte).
    That CONSUMED width, not the decoded rune's would-be re-encoded width, is what [str_range]
    accumulates into byte offsets (review #6 P1 #9): for source [0x80 'A'] Go yields
    [(0,U+FFFD) (1,'A')], and so does the model now (the FFFD consumed ONE byte, not
    [rune_width U+FFFD] = 3).  [str_to_runes] (rune-only) is [map fst] of this — one decoder. *)
Fixpoint str_to_runes_w (s : GoString) : list (GoI32 * int) :=
  match s with
  | EmptyString => nil
  | String c0 r0 =>
      (* [rerr]/[isc] are LOCAL (not top-level Definitions): the whole body is suppressed and lowered by
         name to native [[]rune(s)], so the unsigned [ltb]/[leb] here are proof-only and never extracted. *)
      let rerr := i32wrap 65533%uint63 in              (* U+FFFD *)
      let isc  := fun v => andb (PrimInt63.leb 128%uint63 v) (PrimInt63.ltb v 192%uint63) in  (* cont byte 0x80–0xBF *)
      let v0 := u8raw (ascii_byte c0) in
      if PrimInt63.ltb v0 128%uint63 then              (* 1-byte: ASCII 0x00–0x7F *)
        (i32wrap v0, 1%uint63) :: str_to_runes_w r0
      else if PrimInt63.ltb v0 194%uint63 then         (* 0x80–0xC1: cont-as-lead OR overlong-2 → error *)
        (rerr, 1%uint63) :: str_to_runes_w r0
      else if PrimInt63.ltb v0 224%uint63 then         (* 0xC2–0xDF: 2-byte (result ≥ 0x80, non-overlong) *)
        match r0 with
        | String c1 r1 =>
            let v1 := u8raw (ascii_byte c1) in
            if isc v1 then
              (i32wrap (PrimInt63.lor (PrimInt63.lsl (PrimInt63.land v0 31%uint63) 6%uint63)
                                     (PrimInt63.land v1 63%uint63)), 2%uint63) :: str_to_runes_w r1
            else (rerr, 1%uint63) :: str_to_runes_w r0   (* bad continuation → error, advance 1 *)
        | EmptyString => (rerr, 1%uint63) :: nil         (* truncated → advance 1 (the lead) *)
        end
      else if PrimInt63.ltb v0 240%uint63 then         (* 0xE0–0xEF: 3-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xE0→[0xA0,0xBF] (overlong); 0xED→[0x80,0x9F] (surrogate) *)
              if PrimInt63.eqb v0 224%uint63 then andb (PrimInt63.leb 160%uint63 v1) (PrimInt63.ltb v1 192%uint63)
              else if PrimInt63.eqb v0 237%uint63 then andb (PrimInt63.leb 128%uint63 v1) (PrimInt63.ltb v1 160%uint63)
              else isc v1 in
            match r1' with
            | String c2 r2 =>
                let v2 := u8raw (ascii_byte c2) in
                if andb v1ok (isc v2) then
                  (i32wrap (PrimInt63.lor (PrimInt63.lor
                           (PrimInt63.lsl (PrimInt63.land v0 15%uint63) 12%uint63)
                           (PrimInt63.lsl (PrimInt63.land v1 63%uint63) 6%uint63))
                           (PrimInt63.land v2 63%uint63)), 3%uint63) :: str_to_runes_w r2
                else (rerr, 1%uint63) :: str_to_runes_w r0
            | EmptyString => (rerr, 1%uint63) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%uint63) :: nil
        end
      else if PrimInt63.ltb v0 245%uint63 then         (* 0xF0–0xF4: 4-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xF0→[0x90,0xBF] (overlong); 0xF4→[0x80,0x8F] (>MaxRune) *)
              if PrimInt63.eqb v0 240%uint63 then andb (PrimInt63.leb 144%uint63 v1) (PrimInt63.ltb v1 192%uint63)
              else if PrimInt63.eqb v0 244%uint63 then andb (PrimInt63.leb 128%uint63 v1) (PrimInt63.ltb v1 144%uint63)
              else isc v1 in
            match r1' with
            | String c2 r2' =>
                let v2 := u8raw (ascii_byte c2) in
                match r2' with
                | String c3 r3 =>
                    let v3 := u8raw (ascii_byte c3) in
                    if andb v1ok (andb (isc v2) (isc v3)) then
                      (i32wrap (PrimInt63.lor (PrimInt63.lor (PrimInt63.lor
                               (PrimInt63.lsl (PrimInt63.land v0 7%uint63) 18%uint63)
                               (PrimInt63.lsl (PrimInt63.land v1 63%uint63) 12%uint63))
                               (PrimInt63.lsl (PrimInt63.land v2 63%uint63) 6%uint63))
                               (PrimInt63.land v3 63%uint63)), 4%uint63) :: str_to_runes_w r3
                    else (rerr, 1%uint63) :: str_to_runes_w r0
                | EmptyString => (rerr, 1%uint63) :: str_to_runes_w r0
                end
            | EmptyString => (rerr, 1%uint63) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%uint63) :: nil
        end
      else                                             (* 0xF5–0xFF: invalid lead → error *)
        (rerr, 1%uint63) :: str_to_runes_w r0
  end.
(* rune-only view = drop the consumed-width tags.  A manual fixpoint (not [List.map]) so the
   suppressed body pulls no generic [map] into the extraction closure. *)
Fixpoint str_runes_fst (rs : list (GoI32 * int)) : list GoI32 :=
  match rs with
  | nil              => nil
  | cons (r, _) rest => cons r (str_runes_fst rest)
  end.
Definition str_to_runes (s : GoString) : list GoI32 := str_runes_fst (str_to_runes_w s).
Definition rune_bytes (r : GoI32) : GoString :=
  (* Go's [string(rune)] / [utf8.EncodeRune] replaces an out-of-range or surrogate rune with
     U+FFFD (review #6 P1 #9): [uint32(r) > MaxRune] — a NEGATIVE int32 lands far above MaxRune
     because [i32_norm] sign-extends it into a huge uint63 — or [r] in the UTF-16 surrogate
     range [0xD800,0xDFFF].  Without this the raw bits were emitted as a bogus encoding. *)
  let c0 := i32raw r in
  let c := if andb (PrimInt63.leb c0 1114111%uint63)
                   (negb (andb (PrimInt63.leb 55296%uint63 c0) (PrimInt63.leb c0 57343%uint63)))
           then c0 else 65533%uint63 in
  if PrimInt63.ltb c 128%uint63 then
    String (byte_chr c) EmptyString
  else if PrimInt63.ltb c 2048%uint63 then
    String (byte_chr (PrimInt63.lor 192%uint63 (PrimInt63.lsr c 6%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land c 63%uint63))) EmptyString)
  else if PrimInt63.ltb c 65536%uint63 then
    String (byte_chr (PrimInt63.lor 224%uint63 (PrimInt63.lsr c 12%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land (PrimInt63.lsr c 6%uint63) 63%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land c 63%uint63))) EmptyString))
  else
    String (byte_chr (PrimInt63.lor 240%uint63 (PrimInt63.lsr c 18%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land (PrimInt63.lsr c 12%uint63) 63%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land (PrimInt63.lsr c 6%uint63) 63%uint63)))
   (String (byte_chr (PrimInt63.lor 128%uint63 (PrimInt63.land c 63%uint63))) EmptyString))).
Fixpoint runes_to_str (rs : list GoI32) : GoString :=
  match rs with
  | nil => EmptyString
  | r :: rest => str_concat (rune_bytes r) (runes_to_str rest)
  end.

(** Codec verified by ROUND-TRIP: encode→decode is the identity for ASCII and for a 3-byte
    CJK code point (中 = U+4E2D = 20013, UTF-8 E4 B8 AD). *)
Example rune_roundtrip_ascii :
  str_to_runes (runes_to_str (i32wrap 65%uint63 :: i32wrap 66%uint63 :: nil))
    = i32wrap 65%uint63 :: i32wrap 66%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example rune_roundtrip_cjk :
  str_to_runes (runes_to_str (i32wrap 20013%uint63 :: nil)) = i32wrap 20013%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Break #10 witnesses (machine-checked): INVALID UTF-8 now decodes to U+FFFD (65533) per offending
    byte, advancing ONE byte — exactly Go's [utf8.DecodeRune].  (Before the fix these produced bogus
    code points or swallowed bytes.)  [byte_chr v] is the byte with value [v]. *)
Example utf8_cont_as_lead :                  (* lone continuation 0x80 — not a valid lead → one U+FFFD *)
  str_to_runes (String (byte_chr 128%uint63) EmptyString) = i32wrap 65533%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_overlong_2 :                     (* 0xC0 0x80 (overlong NUL): 0xC0 bad lead, 0x80 cont → two U+FFFD *)
  str_to_runes (String (byte_chr 192%uint63) (String (byte_chr 128%uint63) EmptyString))
    = i32wrap 65533%uint63 :: i32wrap 65533%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_surrogate :                      (* 0xED 0xA0 0x80 (would be U+D800, a UTF-16 surrogate) → three U+FFFD *)
  str_to_runes (String (byte_chr 237%uint63) (String (byte_chr 160%uint63) (String (byte_chr 128%uint63) EmptyString)))
    = i32wrap 65533%uint63 :: i32wrap 65533%uint63 :: i32wrap 65533%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_truncated_2 :                     (* 0xC2 with no continuation → one U+FFFD *)
  str_to_runes (String (byte_chr 194%uint63) EmptyString) = i32wrap 65533%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_valid_2byte :                     (* 0xC2 0xA9 = U+00A9 (©) still decodes correctly *)
  str_to_runes (String (byte_chr 194%uint63) (String (byte_chr 169%uint63) EmptyString)) = i32wrap 169%uint63 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Single rune → string (Go's [string(rune)]): the 1-code-point UTF-8 string.  Reuses the
    [rune_bytes] encoder; lowers to the native [string(rune(r))] (the explicit [rune] cast
    keeps it out of the deprecated [string(int)] form). *)
Definition rune_to_str (r : GoI32) : GoString := rune_bytes r.
Example rune_to_str_ascii : rune_to_str (i32wrap 65%uint63) = "A"%string.
Proof. vm_compute. reflexivity. Qed.
(** Review #6 P1 #9 / minimum-suite #4: an out-of-range or surrogate rune encodes to U+FFFD,
    exactly Go's [string(rune)].  Witnessed against the explicit FFFD encoding [EF BF BD]: a
    UTF-16 surrogate (0xD800), a code point past MaxRune (0x110000), and a NEGATIVE rune (-1,
    built by [i32_sub] so it is a genuine negative int32) all collapse to U+FFFD. *)
Example rune_to_str_surrogate : rune_to_str (i32wrap 55296%uint63) = rune_to_str (i32wrap 65533%uint63).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_above_max : rune_to_str (i32wrap 1114112%uint63) = rune_to_str (i32wrap 65533%uint63).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_negative :
  rune_to_str (i32_sub (i32wrap 0%uint63) (i32wrap 1%uint63)) = rune_to_str (i32wrap 65533%uint63).
Proof. vm_compute. reflexivity. Qed.

(** String COMPARISON (Go spec "Comparison operators": strings are comparable AND
    ordered).  [str_eqb] is Go [==] — byte-sequence equality (a THEOREM via
    [String.eqb]).  [str_ltb] is Go [<] — LEXICOGRAPHIC by BYTE VALUE, exactly Go's
    string ordering: compare byte-by-byte (unsigned 0..255), the first differing byte
    decides, and a proper prefix is [<] the longer string.  Both are pure, total
    operations on immutable byte sequences; the bodies are suppressed and each lowers
    to the bare Go operator ([a == b] / [a < b]).  [str_ltb] reuses the already-
    suppressed [ascii_byte] decoder (so it drags in no [nat_of_ascii]). *)
Definition str_eqb (a b : GoString) : bool := String.eqb a b.

(** Generic [comparable] CONSTRAINT (Go's [func F[K comparable](…)]).  A comparable type's
    equality is carried as a [ComparableW K] WITNESS — computational in Rocq (so [vm_compute] /
    proofs reduce), but the plugin ERASES it: a function with a [ComparableW (Tvar)] parameter
    drops that parameter at its declaration AND every call site, emits the corresponding type
    variable as [K comparable] (not [any]), and lowers the witness equality [cw_eqb] to native
    Go [==].  Faithful: on a Go-comparable type, [cw_eqb] decides the SAME equality [==] does, so
    erasing the dictionary to the native operator preserves meaning (the witness exists only so
    Rocq can compute/prove; Go's [comparable] supplies [==] structurally with no runtime dict). *)
(** Each comparison function DECIDES its type's equality — the evidence a sealed witness must carry. *)
Lemma i64_eqb_spec : forall x y, i64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold i64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply i64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma u64_eqb_spec : forall x y, u64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold u64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply u64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma str_eqb_spec : forall x y, str_eqb x y = true <-> x = y.
Proof. intros x y. unfold str_eqb. apply String.eqb_eq. Qed.

(** SEALED (release-blocking soundness fix, 2026-06-21): [ComparableW] now CARRIES the decidability proof
    [cw_ok] (SProp-erased, proof-irrelevant), so a bogus witness like [MkComparableW (fun _ _ => false) _]
    is UNCONSTRUCTABLE — its spec [forall x y, false = true <-> x = y] is false.  Hence erasing [cw_eqb] to
    native Go [==] is sound, not a forgeable claim.  The proof field erases (SProp), so extraction is
    unchanged: the whole witness is dropped by the plugin regardless of arity. *)
Record ComparableW (K : Type) : Type := MkComparableW {
  cw_eqb : K -> K -> bool ;
  cw_ok  : Squash (forall x y, cw_eqb x y = true <-> x = y) }.
Arguments MkComparableW {K} _ _.
Arguments cw_eqb {K} _.
Arguments cw_ok {K} _.
Definition ceqb {K} (w : ComparableW K) (a b : K) : bool := cw_eqb w a b.
(** Each instance is a [ComparableW]-typed Definition, suppressed by the plugin (the witness erases to
    native [==]); the [squash]ed spec is the seal that makes a bogus witness unconstructable. *)
Definition cw_i64 : ComparableW GoI64    := MkComparableW i64_eqb (squash i64_eqb_spec).
Definition cw_u64 : ComparableW GoU64    := MkComparableW u64_eqb (squash u64_eqb_spec).
Definition cw_str : ComparableW GoString := MkComparableW str_eqb (squash str_eqb_spec).

(** The seal is real (machine-checked): the always-[false] equality does NOT decide [GoI64] equality, so
    no [ComparableW GoI64] can wrap it — the forged witness [MkComparableW (fun _ _ => false) _] is
    unconstructable (its [cw_ok] obligation is the unprovable proposition below).  This is the safe-by-
    construction guarantee the erasure [cw_eqb w → Go ==] needs: a witness exists only when [cw_eqb]
    genuinely decides [=], hence agrees with Go's [==]. *)
Lemma bogus_eqb_undecidable :
  ~ (forall x y : GoI64, (fun _ _ : GoI64 => false) x y = true <-> x = y).
Proof. intro H. destruct (H (i64wrap 0%Z) (i64wrap 0%Z)) as [_ Hb]. discriminate (Hb eq_refl). Qed.

Fixpoint str_ltb (a b : GoString) : bool :=
  match a, b with
  | EmptyString,  EmptyString  => false   (* equal — not [<] *)
  | EmptyString,  String _ _   => true    (* "" < non-empty (prefix) *)
  | String _ _,   EmptyString  => false   (* non-empty not < "" *)
  | String ca ra, String cb rb =>
      let na := u8raw (ascii_byte ca) in  (* byte value 0..255 *)
      let nb := u8raw (ascii_byte cb) in
      if PrimInt63.ltb na nb then true
      else if PrimInt63.ltb nb na then false
      else str_ltb ra rb
  end.

(** Direct [>] / [>=] / [!=] for strings (total lexicographic order, no NaN, so
    [>=] is [¬(<)]).  Recognized by name and lowered to the direct Go operator. *)
Definition str_gtb  (a b : GoString) : bool := str_ltb b a.
Definition str_geb  (a b : GoString) : bool := negb (str_ltb a b).
Definition str_neqb (a b : GoString) : bool := negb (str_eqb a b).

(** Expression switch on a STRING scrutinee — Go's [switch s { case "a": …; default: … }].
    Same shape as [int_switch2] but the equality is [str_eqb] (byte equality); the plugin
    arm is SHARED (it emits the scrutinee and each case value verbatim, Go doing the [==]),
    so int64 and string scrutinees lower identically. *)
Definition str_switch2 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else d.

Example str_switch2_first : forall {B} (k1 k2 d : IO B),
  str_switch2 "a"%string "a"%string k1 "b"%string k2 d = k1.
Proof. reflexivity. Qed.
Example str_switch2_second : forall {B} (k1 k2 d : IO B),
  str_switch2 "b"%string "a"%string k1 "b"%string k2 d = k2.
Proof. reflexivity. Qed.
Example str_switch2_default : forall {B} (k1 k2 d : IO B),
  str_switch2 "z"%string "a"%string k1 "b"%string k2 d = d.
Proof. reflexivity. Qed.

(** N-ary string expression switch (3 cases) — same generalised plugin arm as
    [str_switch2]/[int_switch2]; completes the >2-case coverage for both scrutinee types. *)
Definition str_switch3 {B : Type} (x : GoString)
  (v1 : GoString) (k1 : IO B)
  (v2 : GoString) (k2 : IO B)
  (v3 : GoString) (k3 : IO B)
  (d : IO B) : IO B :=
  if str_eqb x v1 then k1
  else if str_eqb x v2 then k2
  else if str_eqb x v3 then k3
  else d.
Example str_switch3_third : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "c"%string "a"%string k1 "b"%string k2 "c"%string k3 d = k3.
Proof. reflexivity. Qed.
Example str_switch3_default : forall {B} (k1 k2 k3 d : IO B),
  str_switch3 "z"%string "a"%string k1 "b"%string k2 "c"%string k3 d = d.
Proof. reflexivity. Qed.

(** ---- Complex numbers (Go spec "Complex numbers"; the predeclared [complex]/[real]/
    [imag] builtins) ----  A [complex128] is a pair of [float64] components.  We model it
    as a 2-field record over [float]; the plugin renders the type as Go's native
    [complex128] and lowers [go_complex]/[go_real]/[go_imag] to the predeclared builtins
    [complex(re, im)] / [real(c)] / [imag(c)] (the record's struct decl, constructor, and
    projections are all suppressed — recognised by operation name, like the numint
    wrappers).  Construction/extraction are PROVABLE ([go_real (go_complex re im) = re]). *)
Record GoComplex128 : Type := MkComplex128 { c_re : float ; c_im : float }.
Definition go_complex (re im : float) : GoComplex128 := MkComplex128 re im.
Definition go_real (c : GoComplex128) : float := c_re c.
Definition go_imag (c : GoComplex128) : float := c_im c.

Example go_real_complex : forall re im, go_real (go_complex re im) = re.
Proof. reflexivity. Qed.
Example go_imag_complex : forall re im, go_imag (go_complex re im) = im.
Proof. reflexivity. Qed.

(** Complex ARITHMETIC — Go's [+] / [-] on complex128.  These are COMPONENT-WISE (each
    component is a single IEEE float add/sub), so the model is faithful including the
    Inf/NaN corners, and it lowers to the native Go [+] / [-].  *([*] and [/] are DEFERRED:
    Go's complex multiply/divide carry rounding-order subtleties — naive cross-products for
    [*], Smith's scaling algorithm for [/] in the runtime — that a faithful model must match
    exactly; a careful follow-up, not approximated here.)* *)
Definition complex_add (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (PrimFloat.add (c_re a) (c_re b)) (PrimFloat.add (c_im a) (c_im b)).
Definition complex_sub (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (PrimFloat.sub (c_re a) (c_re b)) (PrimFloat.sub (c_im a) (c_im b)).

(** Build-checked: each component of the sum/difference is the float add/sub of the
    corresponding components (so the native [a + b] computes exactly what Go does). *)
Example complex_add_components : forall a b,
  go_real (complex_add a b) = PrimFloat.add (go_real a) (go_real b)
  /\ go_imag (complex_add a b) = PrimFloat.add (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.
Example complex_sub_components : forall a b,
  go_real (complex_sub a b) = PrimFloat.sub (go_real a) (go_real b)
  /\ go_imag (complex_sub a b) = PrimFloat.sub (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.

(** Complex COMPARISON — Go's [==] / [!=] on complex128.  Two complex values are equal iff
    BOTH components are equal (Go spec "Comparison operators"); float [==] is EXACT, so this
    is faithful including the NaN corner ([NaN != NaN] ⇒ a complex with a NaN component is
    never [==] itself).  Lowers to the native Go [==] / [!=]. *)
Definition complex_eqb (a b : GoComplex128) : bool :=
  andb (PrimFloat.eqb (c_re a) (c_re b)) (PrimFloat.eqb (c_im a) (c_im b)).
Definition complex_neqb (a b : GoComplex128) : bool := negb (complex_eqb a b).

(** Build-checked: equality is the component-wise float-[==] conjunction (so the native
    [a == b] decides exactly what Go's complex [==] does). *)
Example complex_eqb_components : forall a b,
  complex_eqb a b = andb (PrimFloat.eqb (go_real a) (go_real b)) (PrimFloat.eqb (go_imag a) (go_imag b)).
Proof. reflexivity. Qed.

(** Complex MULTIPLY — Go's [*] on complex128.  The Go spec underspecifies the rounding of
    complex multiply, and the gc compiler inlines the NAIVE cross-product formula
    [(ac − bd) + (ad + bc)i] (it does NOT implement C99 Annex G's Inf/NaN recovery — only
    DIVISION calls a runtime helper).  This model uses exactly that naive formula, so it
    matches gc bit-for-bit including the Inf/NaN corners (both are naive IEEE), and lowers
    to the native Go [*].  *([/] is still DEFERRED: gc's [runtime.complex128div] uses
    Smith's scaling algorithm — a different computation a faithful model must port exactly.)* *)
Definition complex_mul (a b : GoComplex128) : GoComplex128 :=
  MkComplex128
    (PrimFloat.sub (PrimFloat.mul (c_re a) (c_re b)) (PrimFloat.mul (c_im a) (c_im b)))
    (PrimFloat.add (PrimFloat.mul (c_re a) (c_im b)) (PrimFloat.mul (c_im a) (c_re b))).

(** Build-checked: the real/imag parts are exactly gc's naive cross products. *)
Example complex_mul_components : forall a b,
  go_real (complex_mul a b)
    = PrimFloat.sub (PrimFloat.mul (go_real a) (go_real b)) (PrimFloat.mul (go_imag a) (go_imag b))
  /\ go_imag (complex_mul a b)
    = PrimFloat.add (PrimFloat.mul (go_real a) (go_imag b)) (PrimFloat.mul (go_imag a) (go_real b)).
Proof. intros. split; reflexivity. Qed.

(** Complex unary NEGATION — Go's [-c] on complex128.  Negates BOTH components, each a
    single IEEE float sign-flip [PrimFloat.opp], so faithful including signed zero — note
    [-c] (sign-flip) differs from [(0+0i) - c] on a zero component ([opp (+0) = -0] but
    [0 - (+0) = +0]); we use the sign-flip, matching Go's unary [-].  Lowers to native [-c]. *)
Definition complex_neg (c : GoComplex128) : GoComplex128 :=
  MkComplex128 (PrimFloat.opp (c_re c)) (PrimFloat.opp (c_im c)).

Example complex_neg_components : forall c,
  go_real (complex_neg c) = PrimFloat.opp (go_real c)
  /\ go_imag (complex_neg c) = PrimFloat.opp (go_imag c).
Proof. intros. split; reflexivity. Qed.

(** Complex DIVIDE — Go's [/] on complex128.  Unlike [*] (a naive inline), gc lowers [/]
    to [runtime.complex128div], which uses SMITH'S scaling algorithm (divide through by the
    larger-magnitude denominator component, for numerical stability).  This model is exactly
    that algorithm — operand-for-operand the gc source — so it matches Go for FINITE
    divisors, and it lowers to the native Go [/].  *(Go's runtime ALSO has an Annex-G-style
    Inf/NaN recovery postamble for DEGENERATE divisors — zero / Inf / NaN denominators; the
    native lowering gets that for free at runtime, but this Coq MODEL does not replicate it,
    a documented model gap on degenerate inputs.)* *)
Definition complex_div (n m : GoComplex128) : GoComplex128 :=
  let nr := c_re n in let ni := c_im n in
  let mr := c_re m in let mi := c_im m in
  (* branch on which denominator component is larger in magnitude — Go uses [|mr| >= |mi|], i.e.
     [|mi| <= |mr|].  We compare ABSOLUTE VALUES via [PrimFloat.abs] (a trust-base [PrimFloat.*]
     primitive).  This is sound to use here even though [math.Abs] would need an import: [complex_div]
     lowers to the NATIVE Go [/] (its body is PROOF-ONLY, suppressed by name — see the plugin), so the
     [abs] is never extracted.  (Break #9 fix: the earlier squared form [mi² <= mr²] OVERFLOWED to
     [Inf <= Inf = true] for large operands — |mi|,|mr| ≳ 1e154 — and picked the WRONG branch when
     |mi| > |mr| (e.g. mr=1e160, mi=1e200), diverging from Go on large FINITE divisors.  Abs never
     overflows, so the branch now matches Go's exactly.) *)
  if PrimFloat.leb (PrimFloat.abs mi) (PrimFloat.abs mr) then
    let ratio := PrimFloat.div mi mr in
    let denom := PrimFloat.add mr (PrimFloat.mul ratio mi) in
    MkComplex128 (PrimFloat.div (PrimFloat.add nr (PrimFloat.mul ni ratio)) denom)
                 (PrimFloat.div (PrimFloat.sub ni (PrimFloat.mul nr ratio)) denom)
  else
    let ratio := PrimFloat.div mr mi in
    let denom := PrimFloat.add mi (PrimFloat.mul ratio mr) in
    MkComplex128 (PrimFloat.div (PrimFloat.add (PrimFloat.mul nr ratio) ni) denom)
                 (PrimFloat.div (PrimFloat.sub (PrimFloat.mul ni ratio) nr) denom).

(** Break #9 witness (machine-checked): on a large divisor where BOTH components square to [+Inf]
    (|mi|, |mr| ≳ 1e154) but |mi| > |mr|, the OLD squared-magnitude branch [mi² <= mr²] wrongly reduces
    to [Inf <= Inf = true] (picks the |mr|-branch), while the NEW [|mi| <= |mr|] correctly yields [false]
    (the |mi|-branch) — exactly Go's [|mr| >= |mi|].  ([0x1p550] = 2^550, [0x1p600] = 2^600.) *)
Example complex_div_branch_overflow_fixed :
  let mr := 0x1p550%float in let mi := 0x1p600%float in
     PrimFloat.leb (PrimFloat.mul mi mi) (PrimFloat.mul mr mr) = true    (* old (squared): WRONG branch *)
  /\ PrimFloat.leb (PrimFloat.abs mi)    (PrimFloat.abs mr)    = false.  (* new (abs):     RIGHT branch *)
Proof. vm_compute. split; reflexivity. Qed.

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

(** ---- [ValidWorld]: allocation freshness as a MACHINE-CHECKED invariant (release-blocking break #5) ----

    Every allocator ([map_make]/[map_make_typed]/[make_chan]/[ref_new]) mints [l := w_next w] and bumps
    [w_next] to [l+1].  For "fresh" / "nonzero" / "disjoint" to be THEOREMS rather than comments we carry an
    invariant [ValidWorld]: the allocator pointer is positive (so location 0 is RESERVED — it is Go's [nil])
    AND it bounds the live region (every heap is [None] at and above [w_next]).  Two payoffs follow from the
    invariant ALONE (no side conditions): the next location is nonzero ([valid_fresh_nonzero] — a fresh
    pointer/chan/map is never nil) and is currently unallocated in all three heaps ([valid_fresh_disjoint] —
    a fresh allocation overwrites nothing).  The invariant holds at the initial world ([valid_w_init]) and is
    PRESERVED by every allocator ([valid_alloc_*]) as long as the 63-bit allocator has room to bump
    ([HasRoom]); exhausting 2^63 locations is the documented PrimInt63 substrate limit (the same finiteness
    as [GoI64]), not a soundness gap. *)
Definition ValidWorld (w : World) : Prop :=
  (0 <? w_next w)%uint63 = true /\
  (forall l, (w_next w <=? l)%uint63 = true ->
     w_refs w l = None /\ w_chans w l = None /\ w_maps w l = None).

(** There is room to allocate: [w_next + 1] stays below [wB = 2^63], so the bump does not wrap around to
    a small (already-live or zero) location.  Stated on [to_Z] to avoid a 63-bit int literal. *)
Definition HasRoom (w : World) : Prop := (Uint63.to_Z (w_next w) + 1 < Uint63.wB)%Z.

(** The initial world: empty heaps, allocator at 1 — so location 0 is reserved for [nil]. *)
Definition w_init : World := mkWorld (fun _ => None) (fun _ => None) (fun _ => None) 1%uint63.

Lemma valid_w_init : ValidWorld w_init.
Proof.
  split.
  - now vm_compute.
  - intros l _. unfold w_init; cbn. repeat split; reflexivity.
Qed.

(** PAYOFF 1: the freshly minted location [w_next w] is nonzero — a fresh pointer/chan/map is never [nil]. *)
Lemma valid_fresh_nonzero : forall w, ValidWorld w -> (0 <? w_next w)%uint63 = true.
Proof. intros w [Hpos _]. exact Hpos. Qed.

(** PAYOFF 2: the freshly minted location is currently unallocated in ALL three heaps — so installing a
    cell there (what every allocator does) overwrites nothing; allocations never alias a live object. *)
Lemma valid_fresh_disjoint : forall w, ValidWorld w ->
  w_refs w (w_next w) = None /\ w_chans w (w_next w) = None /\ w_maps w (w_next w) = None.
Proof.
  intros w [_ Hfresh]. apply Hfresh. apply Uint63.leb_spec. lia.
Qed.

(** No-wrap arithmetic: with room to bump, the bump's [to_Z] is exactly [+1] (no modular reduction). *)
Lemma add1_no_wrap : forall x : int, (Uint63.to_Z x + 1 < Uint63.wB)%Z ->
  Uint63.to_Z (PrimInt63.add x 1) = (Uint63.to_Z x + 1)%Z.
Proof.
  intros x H. rewrite Uint63.add_spec. change (Uint63.to_Z 1) with 1%Z.
  pose proof (Uint63.to_Z_bounded x) as Hb.
  apply Z.mod_small. lia.
Qed.

(** Consequences of bumping a has-room pointer past [l']: the OLD pointer is still [<= l'], and [l'] is
    distinct from the freshly minted location (so the install's [eqb] guard is [false] at [l']). *)
Lemma bump_le : forall w l', HasRoom w ->
  (PrimInt63.add (w_next w) 1 <=? l')%uint63 = true -> (w_next w <=? l')%uint63 = true.
Proof.
  intros w l' HR Hle. apply Uint63.leb_spec. apply Uint63.leb_spec in Hle.
  rewrite (add1_no_wrap (w_next w) HR) in Hle. lia.
Qed.

Lemma bump_neq : forall w l', HasRoom w ->
  (PrimInt63.add (w_next w) 1 <=? l')%uint63 = true -> PrimInt63.eqb l' (w_next w) = false.
Proof.
  intros w l' HR Hle. apply Uint63.leb_spec in Hle.
  rewrite (add1_no_wrap (w_next w) HR) in Hle.
  apply Bool.not_true_is_false. intro He. apply Uint63.eqb_spec in He.
  subst l'. lia.
Qed.

(** PRESERVATION: each allocator carries [ValidWorld] to the post-allocation world (given [HasRoom]). *)
Lemma valid_alloc_ref : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  ValidWorld w -> HasRoom w ->
  ValidWorld (mkWorld
    (fun k => if PrimInt63.eqb k (w_next w) then Some (existT _ A (tag, v)) else w_refs w k)
    (w_chans w) (w_maps w) (PrimInt63.add (w_next w) 1)).
Proof.
  intros A tag v w HV HR. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Uint63.ltb_spec. rewrite (add1_no_wrap (w_next w) HR).
    apply Uint63.ltb_spec in Hpos. change (Uint63.to_Z 0) with 0%Z in *.
    pose proof (Uint63.to_Z_bounded (w_next w)). lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%uint63 = true) by (apply (bump_le w l' HR Hle)).
    assert (Hneq : PrimInt63.eqb l' (w_next w) = false) by (apply (bump_neq w l' HR Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_chan : forall {A} (tag : GoTypeTag A) (w : World),
  ValidWorld w -> HasRoom w ->
  ValidWorld (mkWorld (w_refs w)
    (fun k => if PrimInt63.eqb k (w_next w) then Some (existT _ A (tag, (nil, false))) else w_chans w k)
    (w_maps w) (PrimInt63.add (w_next w) 1)).
Proof.
  intros A tag w HV HR. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Uint63.ltb_spec. rewrite (add1_no_wrap (w_next w) HR).
    apply Uint63.ltb_spec in Hpos. change (Uint63.to_Z 0) with 0%Z in *.
    pose proof (Uint63.to_Z_bounded (w_next w)). lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%uint63 = true) by (apply (bump_le w l' HR Hle)).
    assert (Hneq : PrimInt63.eqb l' (w_next w) = false) by (apply (bump_neq w l' HR Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

Lemma valid_alloc_map_bump : forall (w : World),
  ValidWorld w -> HasRoom w ->
  ValidWorld (mkWorld (w_refs w) (w_chans w) (w_maps w) (PrimInt63.add (w_next w) 1)).
Proof.
  intros w HV HR. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Uint63.ltb_spec. rewrite (add1_no_wrap (w_next w) HR).
    apply Uint63.ltb_spec in Hpos. change (Uint63.to_Z 0) with 0%Z in *.
    pose proof (Uint63.to_Z_bounded (w_next w)). lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    apply Hfresh. apply (bump_le w l' HR Hle).
Qed.

Lemma valid_alloc_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World),
  ValidWorld w -> HasRoom w ->
  ValidWorld (mkWorld (w_refs w) (w_chans w)
    (fun k => if PrimInt63.eqb k (w_next w)
              then Some (0%uint63, existT _ K (kt, existT _ V (vt, fun _ => None))) else w_maps w k)
    (PrimInt63.add (w_next w) 1)).
Proof.
  intros K V kt vt w HV HR. destruct HV as [Hpos Hfresh]. split.
  - cbn [w_next]. apply Uint63.ltb_spec. rewrite (add1_no_wrap (w_next w) HR).
    apply Uint63.ltb_spec in Hpos. change (Uint63.to_Z 0) with 0%Z in *.
    pose proof (Uint63.to_Z_bounded (w_next w)). lia.
  - intros l' Hle. cbn [w_next w_refs w_chans w_maps] in *.
    assert (Hle0 : (w_next w <=? l')%uint63 = true) by (apply (bump_le w l' HR Hle)).
    assert (Hneq : PrimInt63.eqb l' (w_next w) = false) by (apply (bump_neq w l' HR Hle)).
    destruct (Hfresh l' Hle0) as [Hr [Hc Hm]].
    rewrite Hneq. repeat split; assumption.
Qed.

(** The invariant is genuinely INDUCTIVE across the REAL allocator API (not just the world-shapes above):
    running any allocator on a valid, has-room world yields a valid world.  With [valid_w_init] this means
    EVERY world reachable by a finite allocation sequence is valid — so [valid_fresh_nonzero] /
    [valid_fresh_disjoint] apply at every allocation, making "fresh ⇒ nonzero ∧ disjoint" a theorem about
    [ref_new]/[make_chan]/[map_make]/[map_make_typed] BY NAME.  (Break #5: freshness ESTABLISHED, not asserted.) *)
Corollary valid_run_ref_new : forall {A} (tag : GoTypeTag A) (v : A) (w : World) r w',
  ValidWorld w -> HasRoom w -> run_io (ref_new tag v) w = ORet r w' -> ValidWorld w'.
Proof.
  intros A tag v w r w' HV HR Hrun. unfold run_io, ref_new in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_ref; assumption.
Qed.

Corollary valid_run_make_chan : forall {A} (tag : GoTypeTag A) (w : World) r w',
  ValidWorld w -> HasRoom w -> run_io (make_chan tag) w = ORet r w' -> ValidWorld w'.
Proof.
  intros A tag w r w' HV HR Hrun. unfold run_io, make_chan in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_chan; assumption.
Qed.

Corollary valid_run_map_typed : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) r w',
  ValidWorld w -> HasRoom w -> run_io (map_make_typed kt vt) w = ORet r w' -> ValidWorld w'.
Proof.
  intros K V kt vt w r w' HV HR Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_map_typed; assumption.
Qed.

Corollary valid_run_map_make : forall {K V} (w : World) r w',
  ValidWorld w -> HasRoom w -> run_io (@map_make K V) w = ORet r w' -> ValidWorld w'.
Proof.
  intros K V w r w' HV HR Hrun. unfold run_io, map_make in Hrun.
  injection Hrun as _ Hw. subst w'. apply valid_alloc_map_bump; assumption.
Qed.

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

(** ---- Pointers (Go spec "Pointer types", Phase B1) ----

    A Go pointer [*T] is a typed heap LOCATION.  It shares the [w_refs] cell heap with
    [Ref] — both are heap locations — but lowers DIFFERENTLY: a [Ref] is a local Go
    variable (one cell, no aliasing across copies), whereas a [Ptr] lowers to Go [*T],
    so COPYING a pointer makes two handles to the SAME cell (aliasing — the defining
    pointer behaviour).  A [Ptr] may be nil ([ptr_nil], location 0); dereferencing nil
    panics (Go's nil-pointer panic) — the raw [ptr_get]/[ptr_set] are the escape hatch,
    [ptr_get_ok] (below) the safe-by-construction comma-ok form.

    [Ptr A] is its own record so it is a DISTINCT type the plugin renders [*T]; its ops
    go through the SAME [ref_sel]/[ref_upd] (via [ptr_as_ref]), so read-after-write and
    aliasing are inherited from [ref_sel_upd_same] — no new heap, no new axiom. *)
(** [ptr_as_ref tag p]: view a (tag-free) [Ptr A] as a [Ref A] at the same location with the GIVEN
    tag — so the deref ops reuse the [ref_sel]/[ref_upd] heap (read-after-write, aliasing inherited). *)
Definition ptr_as_ref {A} (tag : GoTypeTag A) (p : Ptr A) : Ref A := mkRef (p_loc p) tag.
Definition ptr_nil {A} (tag : GoTypeTag A) : Ptr A := mkPtr 0%uint63.
(* A TAG-FREE nil pointer (for a NAMED/recursive type that has no [GoTypeTag], e.g. a recursive
   struct's self-pointer field): same nil handle, but needs no tag.  Lowers to a bare Go [nil] (valid
   where the target type is known — a struct-literal field / typed slot).  The [unit] arg makes it a
   recognizable application at the call site. *)
Definition ptr_nil_tf {A} (_ : unit) : Ptr A := mkPtr 0%uint63.

(** [ptr_new tag v]: Go [p := new(T); *p = v] — allocate a FRESH (nonzero) location,
    store [v] (tagged), bump the allocator, return the pointer.  Fresh ⇒ never nil. *)
Definition ptr_new {A} (tag : GoTypeTag A) (v : A) : IO (Ptr A) :=
  fun w => let l := w_next w in
           ORet (mkPtr l)
                (mkWorld (fun k => if PrimInt63.eqb k l then Some (existT _ A (tag, v))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (PrimInt63.add l 1%uint63)).
(** [new(T)] (Go's predeclared [new]): allocate a FRESH [*T] pointing to the ZERO value
    of [T], return it.  = [ptr_new tag (zero_val tag)] — fresh, hence never nil; the
    pointee reads as the zero value.  Lowers to Go [new(T)]. *)
Definition go_new {A} (tag : GoTypeTag A) : IO (Ptr A) := ptr_new tag (zero_val tag).

(** [ptr_get tag p] = [*p] (deref read); [ptr_set tag p v] = [*p = v] (deref write).  Both take the
    pointee tag explicitly (the tag-free handle does not carry it). *)
(** Break #6 (pointers): the RAW deref/assign now PANIC on a nil pointer, faithful to Go's [*p] /
    [*p = v] (which panic on nil) — closing the old "fabricate a zero / silently write loc 0" gap.  The
    nil sentinel is location 0, which [ValidWorld] RESERVES (no allocation ever returns it — break #5),
    so the [eqb (p_loc p) 0] guard exactly separates "live cell" from "nil".  These are the catch-able
    escape hatches (rule 4); [ptr_get_ok] is the safe-by-construction comma-ok form. *)
Definition ptr_get {A} (tag : GoTypeTag A) (p : Ptr A) : IO A :=
  fun w => if PrimInt63.eqb (p_loc p) 0%uint63 then OPanic (any tt) w
           else ORet (ref_sel (ptr_as_ref tag p) w) w.
Definition ptr_set {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) : IO unit :=
  fun w => if PrimInt63.eqb (p_loc p) 0%uint63 then OPanic (any tt) w
           else ORet tt (ref_upd (ptr_as_ref tag p) v w).
Lemma run_ptr_get : forall {A} (tag : GoTypeTag A) (p : Ptr A) (w : World),
  run_io (ptr_get tag p) w =
    if PrimInt63.eqb (p_loc p) 0%uint63 then OPanic (any tt) w
    else ORet (ref_sel (ptr_as_ref tag p) w) w.
Proof. reflexivity. Qed.
Lemma run_ptr_set : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  run_io (ptr_set tag p v) w =
    if PrimInt63.eqb (p_loc p) 0%uint63 then OPanic (any tt) w
    else ORet tt (ref_upd (ptr_as_ref tag p) v w).
Proof. reflexivity. Qed.

(** Faithfulness: dereferencing / assigning through a NIL pointer PANICS, exactly as Go's [*nil]. *)
Lemma ptr_get_nil : forall {A} (tag : GoTypeTag A) (w : World),
  run_io (ptr_get tag (ptr_nil tag)) w = OPanic (any tt) w.
Proof. reflexivity. Qed.
Lemma ptr_set_nil : forall {A} (tag : GoTypeTag A) (v : A) (w : World),
  run_io (ptr_set tag (ptr_nil tag) v) w = OPanic (any tt) w.
Proof. reflexivity. Qed.

(** Read-after-write THROUGH a pointer — a THEOREM (inherited from the shared heap): after
    [ptr_set tag p v], [ptr_get tag p] returns [v].  Holds for ALL [p]: on a nil pointer BOTH sides
    panic at the [ptr_set] step (so they agree), and on a live pointer the read observes the write. *)
Lemma ptr_get_set_same : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A),
  bind (ptr_set tag p v) (fun _ => ptr_get tag p) =
  bind (ptr_set tag p v) (fun _ => ret v).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, !run_ptr_set.
  destruct (PrimInt63.eqb (p_loc p) 0%uint63) eqn:Hnil.
  - reflexivity.
  - cbn. rewrite run_ptr_get, Hnil, ref_sel_upd_same, run_ret. reflexivity.
Qed.

(** ---- [&x]: the ADDRESS-OF operator (Go's `&`) — the missing inverse of [ptr_as_ref] ----

    Taking the address of a local variable [x] (a [Ref A]) yields a [*T] ([Ptr A]) aliasing x's cell.
    A [Ref] and a [Ptr] share the SAME [w_refs] heap (a [Ref] is a Go local, a [Ptr] its `*T` handle), so
    [&x] is simply the [Ref]'s location wrapped as a (tag-free) [Ptr] — [ptr_as_ref]'s inverse.  KEY SAFETY
    PROPERTY: a [Ref] always lives at a NONZERO location ([ValidWorld] reserves 0 for nil — break #5), so
    [&x] is NEVER nil; dereferencing it therefore never panics.  Taking an address is ALWAYS safe (unlike a
    raw [*T], which may be nil).  Read/write THROUGH [&x] alias [x] — the defining pointer behaviour —
    inherited from the shared heap, no new axiom. *)
Definition ref_as_ptr {A} (r : Ref A) : Ptr A := mkPtr (r_loc r).

Lemma ref_as_ptr_loc : forall {A} (r : Ref A), p_loc (ref_as_ptr r) = r_loc r.
Proof. reflexivity. Qed.

(* Viewing [&x] back as a [Ref] (with x's own tag) recovers [x] exactly — same location, same tag. *)
Lemma ptr_as_ref_of_ref_as_ptr : forall {A} (r : Ref A),
  ptr_as_ref (r_tag r) (ref_as_ptr r) = r.
Proof. intros A [l tag]. reflexivity. Qed.

(* [&x] is never nil (a [Ref]'s location is nonzero), so it is SAFE to dereference — never panics. *)
Lemma ref_as_ptr_not_nil : forall {A} (r : Ref A),
  r_loc r <> 0%uint63 -> p_loc (ref_as_ptr r) <> 0%uint63.
Proof. intros A r Hnz. rewrite ref_as_ptr_loc. exact Hnz. Qed.

(* READ through [&x]: [*(&x)] reads [x]'s value (with x's tag) and NEVER panics. *)
Lemma ptr_get_ref_as_ptr : forall {A} (r : Ref A) (w : World),
  r_loc r <> 0%uint63 ->
  run_io (ptr_get (r_tag r) (ref_as_ptr r)) w = ORet (ref_sel r w) w.
Proof.
  intros A r w Hnz. rewrite run_ptr_get, ref_as_ptr_loc.
  rewrite (Uint63.eqb_false_complete (r_loc r) 0%uint63 Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr. reflexivity.
Qed.

(* WRITE through [&x]: [*(&x) = v] updates [x]'s OWN cell and never panics. *)
Lemma ptr_set_ref_as_ptr : forall {A} (r : Ref A) (v : A) (w : World),
  r_loc r <> 0%uint63 ->
  run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt (ref_upd r v w).
Proof.
  intros A r v w Hnz. rewrite run_ptr_set, ref_as_ptr_loc.
  rewrite (Uint63.eqb_false_complete (r_loc r) 0%uint63 Hnz).
  rewrite ptr_as_ref_of_ref_as_ptr. reflexivity.
Qed.

(* THE DEFINING ALIAS: writing through [&x] is visible at [x] — [*(&x) = v], then [x] reads back [v].
   This is the whole point of taking an address: the pointer and the variable share one cell. *)
Theorem ptr_set_ref_as_ptr_aliases : forall {A} (r : Ref A) (v : A) (w : World),
  r_loc r <> 0%uint63 ->
  exists w', run_io (ptr_set (r_tag r) (ref_as_ptr r) v) w = ORet tt w' /\ ref_sel r w' = v.
Proof.
  intros A r v w Hnz. exists (ref_upd r v w). split.
  - exact (ptr_set_ref_as_ptr r v w Hnz).
  - apply ref_sel_upd_same.
Qed.

(** ---- CLOSED-WORLD nil-safety: the modeled nil panics are UNREACHABLE for ALLOCATED handles ----

    Modeling the nil panic (in [ptr_get]/[ptr_set]/[map_set]) plays TWO roles.  (1) COMPLETENESS: it is
    faithful to Go's [*nil] / nil-map-write.  (2) DEFENCE: it is a cheap RUNTIME guard for the future
    OPEN WORLD (imports), where proofs will rest on axioms about external code that could be WRONG — the
    check turns a bad assumption (an import handing back nil where we assumed non-nil) into a loud panic
    rather than silent heap corruption.  But in the CLOSED WORLD — every handle minted by an allocator —
    the "oops" must never fire: break #5 ([valid_fresh_nonzero]) proves a freshly minted location is
    nonzero, so an allocated pointer/map is provably non-nil and the op takes the heap branch, NEVER
    [OPanic].  ([ptr_alloc_assign_no_panic] / [map_alloc_set_no_panic] are that guarantee.)  The OPEN-WORLD
    boundary — a function handed an ARBITRARY handle — still guards via [ptr_get_ok] / [ptr_is_nil] before
    crossing in.  (Goal: NO panic class — nil, div-by-zero, OOB, send-on-closed — is reachable in a
    well-formed closed-world program; the evidence-carrying APIs ([div_nz], [slice_at], here) are the bricks.) *)
Lemma pos_neq0 : forall x : int, (0 <? x)%uint63 = true -> PrimInt63.eqb x 0%uint63 = false.
Proof.
  intros x H. apply Bool.not_true_is_false. intro He.
  apply Uint63.eqb_spec in He. subst x.
  apply Uint63.ltb_spec in H. change (Uint63.to_Z 0) with 0%Z in H. lia.
Qed.

(** An ALLOCATED pointer is non-nil (its handle is the old [w_next], nonzero by break #5). *)
Lemma ptr_new_nonzero : forall {A} (tag : GoTypeTag A) (v : A) (w : World) p w',
  ValidWorld w -> run_io (ptr_new tag v) w = ORet p w' -> PrimInt63.eqb (p_loc p) 0%uint63 = false.
Proof.
  intros A tag v w p w' HV Hrun. unfold run_io, ptr_new in Hrun. cbv zeta in Hrun.
  injection Hrun as Hp _. subst p. cbn [p_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.

(** On a non-nil pointer the panic branch is DEAD — deref/assign just hit the heap. *)
Lemma ptr_set_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (v : A) (w : World),
  PrimInt63.eqb (p_loc p) 0%uint63 = false ->
  run_io (ptr_set tag p v) w = ORet tt (ref_upd (ptr_as_ref tag p) v w).
Proof. intros A tag p v w Hnn. rewrite run_ptr_set, Hnn. reflexivity. Qed.
Lemma ptr_get_nonnil : forall {A} (tag : GoTypeTag A) (p : Ptr A) (w : World),
  PrimInt63.eqb (p_loc p) 0%uint63 = false ->
  run_io (ptr_get tag p) w = ORet (ref_sel (ptr_as_ref tag p) w) w.
Proof. intros A tag p w Hnn. rewrite run_ptr_get, Hnn. reflexivity. Qed.

(** CLOSED-WORLD GUARANTEE: allocate a pointer, then assign through it — provably NO panic. *)
Corollary ptr_alloc_assign_no_panic : forall {A} (tag : GoTypeTag A) (v v' : A) (w : World) p w',
  ValidWorld w -> run_io (ptr_new tag v) w = ORet p w' ->
  exists w'', run_io (ptr_set tag p v') w' = ORet tt w''.
Proof.
  intros A tag v v' w p w' HV Hrun. eexists.
  apply ptr_set_nonnil, (ptr_new_nonzero tag v w p w' HV Hrun).
Qed.

(** The map analogues: an allocated map is non-nil, so [map_set] on it never panics. *)
Lemma map_make_typed_nonzero : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (w : World) m w',
  ValidWorld w -> run_io (map_make_typed kt vt) w = ORet m w' -> PrimInt63.eqb (gm_loc m) 0%uint63 = false.
Proof.
  intros K V kt vt w m w' HV Hrun. unfold run_io, map_make_typed in Hrun. cbv zeta in Hrun.
  injection Hrun as Hm _. subst m. cbn [gm_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
Lemma map_set_nonnil : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (m : GoMap K V) (w : World),
  PrimInt63.eqb (gm_loc m) 0%uint63 = false ->
  run_io (map_set kt vt k v m) w = ORet tt (map_upd kt vt k v m w).
Proof. intros K V kt vt k v m w Hnn. rewrite run_map_set, Hnn. reflexivity. Qed.
Corollary map_alloc_set_no_panic : forall {K V} (kt : GoTypeTag K) (vt : GoTypeTag V) (k : K) (v : V) (w : World) m w',
  ValidWorld w -> run_io (map_make_typed kt vt) w = ORet m w' ->
  exists w'', run_io (map_set kt vt k v m) w' = ORet tt w''.
Proof.
  intros K V kt vt k v w m w' HV Hrun. eexists.
  apply map_set_nonnil, (map_make_typed_nonzero kt vt w m w' HV Hrun).
Qed.

(** Channel analogue: an ALLOCATED channel is non-nil ([make_chan] mints the old [w_next], nonzero by
    break #5), so [close] on it never hits the nil panic.  [chan_alloc_close_no_panic] is the guarantee
    (the remaining [close] panic — double-close — is the send-on-closed class, gated separately by
    [chan_closed]).  [send]/[recv] on the same allocated channel likewise never hit the nil case. *)
Lemma make_chan_nonzero : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  ValidWorld w -> run_io (make_chan tag) w = ORet ch w' -> PrimInt63.eqb (ch_loc ch) 0%uint63 = false.
Proof.
  intros A tag w ch w' HV Hrun. unfold run_io, make_chan in Hrun. cbv zeta in Hrun.
  injection Hrun as Hc _. subst ch. cbn [ch_loc]. apply pos_neq0, (valid_fresh_nonzero w HV).
Qed.
Corollary chan_alloc_close_no_panic : forall {A} (tag : GoTypeTag A) (w : World) ch w',
  ValidWorld w -> run_io (make_chan tag) w = ORet ch w' -> chan_closed ch w' = false ->
  exists w'', run_io (close_chan tag ch) w' = ORet tt w''.
Proof.
  intros A tag w ch w' HV Hrun Hcl. eexists.
  apply run_close; [ apply (make_chan_nonzero tag w ch w' HV Hrun) | exact Hcl ].
Qed.

(** ALIASING — the defining pointer property, a THEOREM: two pointers at the SAME
    location ([p] and a copy [q]) see each other's writes.  A write through [q] is
    observed by a read through [p] — impossible for a non-aliasing [Ref] var. *)
Lemma ptr_alias : forall {A} (tag : GoTypeTag A) (p q : Ptr A) (v : A) (w : World),
  p_loc p = p_loc q ->
  ref_sel (ptr_as_ref tag p) (ref_upd (ptr_as_ref tag q) v w) = v.
Proof.
  intros A tag p q v w Hl.
  unfold ptr_as_ref. rewrite Hl.
  apply (ref_sel_upd_same (mkRef (p_loc q) tag) v w).
Qed.

(** ---- nil-deref SAFETY (Phase B1b) ----

    Dereferencing a nil pointer PANICS in Go.  The raw [ptr_get]/[ptr_set] are the
    escape hatch; [ptr_get_ok] is the safe-by-construction default — a comma-ok CPS
    form (like [slice_at_ok]/[recv_ok]) that BRANCHES on [p ≠ nil]: non-nil ⇒
    [v = *p, ok = true]; nil ⇒ [v = zero, ok = false].  Because the caller must handle
    [ok = false], the nil-deref panic is UNREACHABLE.  (A [Ptr] is nil iff its location
    is the 0 sentinel — [ptr_nil].  The value is in the world heap, so [ptr_get_ok]
    threads [w]; a read leaves [w] unchanged.) *)
Definition ptr_is_nil {A} (p : Ptr A) : bool := PrimInt63.eqb (p_loc p) 0%uint63.

Definition ptr_get_ok {A B} (tag : GoTypeTag A) (p : Ptr A) (k : A -> bool -> IO B) : IO B :=
  fun w => if ptr_is_nil p
           then k (zero_val tag) false w
           else k (ref_sel (ptr_as_ref tag p) w) true w.

(** Dereferencing a NIL pointer takes the SAFE branch ([ok = false], [v = zero]) —
    never the panic; the nil case is forced on the caller.  A THEOREM. *)
Lemma ptr_get_ok_nil : forall {A B} (tag : GoTypeTag A) (k : A -> bool -> IO B),
  ptr_get_ok tag (ptr_nil tag) k = k (zero_val tag) false.
Proof.
  intros A B tag k. unfold ptr_get_ok, ptr_is_nil, ptr_nil. reflexivity.
Qed.

(** A pointer from [ptr_new] is NON-nil, so [ptr_get_ok] reads through it
    ([ok = true]) and returns the stored value: safe deref of a live pointer. *)
Lemma ptr_get_ok_nonnil : forall {A B} (tag : GoTypeTag A) (p : Ptr A)
    (k : A -> bool -> IO B) (w : World),
  ptr_is_nil p = false ->
  ptr_get_ok tag p k w = k (ref_sel (ptr_as_ref tag p) w) true w.
Proof. intros A B tag p k w Hnn. unfold ptr_get_ok. rewrite Hnn. reflexivity. Qed.

(** ---- Slices as ALIASING HANDLES (Go spec "Slice types", Phase B3) ----

    A Go slice is NOT a value — it is a HANDLE [(backing-array, offset, len, cap)] that
    SHARES its backing array, so sub-slicing and writes ALIAS.  The list-based [GoSlice]
    (a value, no aliasing) stays for the immutable cases; [SliceH] is the faithful
    aliasing model.  Backing arrays REUSE the [w_refs] cell heap: element [i] of a
    [SliceH] is the cell at [base + offset + i].  Sub-slicing shifts [offset] over the
    SAME cells, so [sub-slice[j] = parent[a+j]] is the SAME cell — aliasing is then the
    `ref_sel_upd_same` theorem, no new heap, no new axiom.  Lowers to Go [[]T] (which
    IS this handle) with native [make]/index/sub-slice. *)
Record SliceH (A : Type) : Type := mkSliceH
  { sh_base : int ; sh_off : int ; sh_len : int ; sh_cap : int ; sh_tag : GoTypeTag A }.
Arguments mkSliceH {A} _ _ _ _ _.
Arguments sh_base {A} _.  Arguments sh_off {A} _.  Arguments sh_len {A} _.
Arguments sh_cap {A} _.   Arguments sh_tag {A} _.

(* Element [i]'s cell = [base + (off + i)] — grouped so the sub-slice alias is one
   [add_assoc].  [sh_cell] is the [Ref] view into the shared heap. *)
Definition sh_loc {A} (s : SliceH A) (i : int) : int :=
  PrimInt63.add (sh_base s) (PrimInt63.add (sh_off s) i).
Definition sh_cell {A} (s : SliceH A) (i : int) : Ref A := mkRef (sh_loc s i) (sh_tag s).

(* [make([]T, n)]: allocate [n] fresh consecutive zeroed cells, return the handle. *)
Definition slice_make_h {A} (tag : GoTypeTag A) (n : int) : IO (SliceH A) :=
  fun w => let base := w_next w in
           ORet (mkSliceH base 0 n n tag)
                (mkWorld (fun k => if (PrimInt63.leb base k
                                       && PrimInt63.ltb k (PrimInt63.add base n))%bool
                                   then Some (existT _ A (tag, zero_val tag))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (PrimInt63.add base n)).
(* [s[i]] read / [s[i] = v] write, through the shared backing cell. *)
Definition slice_idx_get {A} (tag : GoTypeTag A) (s : SliceH A) (i : int) : IO A :=
  fun w => ORet (ref_sel (sh_cell s i) w) w.
Definition slice_idx_set {A} (s : SliceH A) (i : int) (v : A) : IO unit :=
  fun w => ORet tt (ref_upd (sh_cell s i) v w).
Lemma run_slice_idx_get : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : int) (w : World),
  run_io (slice_idx_get tag s i) w = ORet (ref_sel (sh_cell s i) w) w.
Proof. reflexivity. Qed.
Lemma run_slice_idx_set : forall {A} (s : SliceH A) (i : int) (v : A) (w : World),
  run_io (slice_idx_set s i v) w = ORet tt (ref_upd (sh_cell s i) v w).
Proof. reflexivity. Qed.
(* [s[a:b]]: same backing [base], [offset] shifted by [a] — SHARES the cells. *)
Definition subslice {A} (s : SliceH A) (a b : int) : SliceH A :=
  mkSliceH (sh_base s) (PrimInt63.add (sh_off s) a)
           (PrimInt63.sub b a) (PrimInt63.sub (sh_cap s) a) (sh_tag s).

(** Sub-slice element [j] IS parent element [a+j] — the SAME backing cell. *)
Lemma subslice_shares_cell : forall {A} (s : SliceH A) (a b j : int),
  sh_cell (subslice s a b) j = sh_cell s (PrimInt63.add a j).
Proof.
  intros A s a b j. unfold sh_cell, sh_loc, subslice. cbn.
  rewrite (Uint63.add_assoc (sh_off s) a j). reflexivity.
Qed.

(** ALIASING — the defining slice property, a THEOREM: a write through a SUB-SLICE is
    observed through the PARENT (they share the backing array).  Write [sub[j]] (=
    [parent[a+j]]), read [parent[a+j]] → the written value. *)
Lemma subslice_alias : forall {A} (s : SliceH A) (a b j : int) (v : A) (w : World),
  ref_sel (sh_cell s (PrimInt63.add a j))
          (ref_upd (sh_cell (subslice s a b) j) v w) = v.
Proof.
  intros A s a b j v w. rewrite subslice_shares_cell. apply ref_sel_upd_same.
Qed.

(** SEPARATION — the COMPLEMENT of aliasing, equally defining for a faithful reference-type model: a
    write to cell [i] of slice [s] leaves cell [j] of slice [s'] UNCHANGED whenever they are DIFFERENT
    backing cells ([sh_loc s i <> sh_loc s' j]).  So aliasing holds exactly where the cells COINCIDE
    ([subslice_alias]) and independence exactly where they DIFFER — e.g. a write to [s[0:2]] is
    invisible through [s[2:4]], and writes to distinct indices of one slice don't interfere. *)
Lemma slice_idx_set_frame : forall {A B} (s : SliceH A) (s' : SliceH B) (i j : int) (v : A) (w : World),
  sh_loc s i <> sh_loc s' j ->
  ref_sel (sh_cell s' j) (ref_upd (sh_cell s i) v w) = ref_sel (sh_cell s' j) w.
Proof.
  intros A B s s' i j v w Hne. unfold ref_sel, ref_upd, sh_cell. cbn [r_loc r_tag w_refs].
  destruct (PrimInt63.eqb (sh_loc s' j) (sh_loc s i)) eqn:E; [|reflexivity].
  apply Uint63.eqb_spec in E. exfalso. apply Hne. symmetry. exact E.
Qed.

(** Read-after-write at an index — a THEOREM (from the shared heap). *)
Lemma slice_idx_get_set_same : forall {A} (tag : GoTypeTag A) (s : SliceH A) (i : int) (v : A),
  bind (slice_idx_set s i v) (fun _ => slice_idx_get tag s i) =
  bind (slice_idx_set s i v) (fun _ => ret v).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, run_slice_idx_set. cbn.
  rewrite run_slice_idx_get, ref_sel_upd_same, run_ret. reflexivity.
Qed.

(** [append(s, v)] (Phase B3b) — the SUBTLE Go semantics:
    - WITHIN cap ([len < cap]): writes the cell at index [len] IN PLACE and returns a
      [len+1] handle over the SAME backing — so it ALIASES the original (and any
      sub-slice sharing those cells).
    - PAST cap ([len = cap]): REALLOCATES a fresh backing of [len+1] cells (at the
      fresh [w_next], DISJOINT from the old), copies the old elements, appends [v] —
      so the result does NOT alias the original.
    Lowers to Go's native [append(s, v)] (which makes exactly this choice on [cap]). *)
Definition slice_append {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) : IO (SliceH A) :=
  fun w =>
    if (sh_len s <? sh_cap s)%uint63
    then (* in place: write index len, len+1, SAME base/off/cap *)
      ORet (mkSliceH (sh_base s) (sh_off s) (PrimInt63.add (sh_len s) 1) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w)
    else (* reallocate: fresh disjoint backing of len+1, copy old, append v *)
      let base' := w_next w in
      let n := sh_len s in
      ORet (mkSliceH base' 0 (PrimInt63.add n 1) (PrimInt63.add n 1) tag)
           (mkWorld (fun k =>
              if (PrimInt63.leb base' k
                  && PrimInt63.ltb k (PrimInt63.add base' (PrimInt63.add n 1)))%bool
              then (let j := PrimInt63.sub k base' in
                    if PrimInt63.eqb j n
                    then Some (existT _ A (tag, v))                         (* the appended element *)
                    else Some (existT _ A (tag, ref_sel (sh_cell s j) w)))  (* a copy of old s[j] *)
              else w_refs w k)
              (w_chans w) (w_maps w) (PrimInt63.add base' (PrimInt63.add n 1))).

(** WITHIN-cap append is IN PLACE: it updates exactly [s]'s cell at index [len], so the
    new element is written into the SHARED backing — a THEOREM.  (Reading [result[len]]
    or [parent[off+len]] sees [v].) *)
Lemma slice_append_incap : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_len s <? sh_cap s)%uint63 = true ->
  run_io (slice_append tag s v) w
    = ORet (mkSliceH (sh_base s) (sh_off s) (PrimInt63.add (sh_len s) 1) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w).
Proof. intros A tag s v w Hlt. unfold slice_append, run_io. rewrite Hlt. reflexivity. Qed.

(** ...and that in-place write is OBSERVED through the parent backing: reading the cell
    at index [len] after the append returns [v] (the appended element aliases). *)
Lemma slice_append_incap_aliases : forall {A} (tag : GoTypeTag A) (s : SliceH A) (v : A) (w : World),
  (sh_len s <? sh_cap s)%uint63 = true ->
  ref_sel (sh_cell s (sh_len s))
          (match run_io (slice_append tag s v) w with ORet _ w' => w' | OPanic _ w' => w' end) = v.
Proof.
  intros A tag s v w Hlt. rewrite slice_append_incap by exact Hlt. cbn.
  apply ref_sel_upd_same.
Qed.

(** [make([]T, len, cap)] (Phase B3c): allocate [cap] fresh zeroed cells; the handle
    has length [len] and capacity [cap] (so it has [cap - len] spare slots — appending
    within them is IN PLACE, [slice_append_incap]).  Same heap shape as [slice_make_h]
    (which is the [len = cap] case), but distinguishes len from cap. *)
Definition slice_make_lc {A} (tag : GoTypeTag A) (len cap : int) : IO (SliceH A) :=
  fun w => let base := w_next w in
           ORet (mkSliceH base 0 len cap tag)
                (mkWorld (fun k => if (PrimInt63.leb base k
                                       && PrimInt63.ltb k (PrimInt63.add base cap))%bool
                                   then Some (existT _ A (tag, zero_val tag))
                                   else w_refs w k)
                         (w_chans w) (w_maps w) (PrimInt63.add base cap)).

(** A [make([]T, len, cap)] slice has spare capacity, so [append] is IN PLACE and the
    result SHARES its backing — a THEOREM directly from [slice_append_incap]: the append
    writes the cell at index [len] of the ORIGINAL handle. *)
Lemma make_lc_append_inplace : forall {A} (tag : GoTypeTag A) (len cap : int) (v : A) (w : World),
  (len <? cap)%uint63 = true ->
  forall s w0, run_io (slice_make_lc tag len cap) w = ORet s w0 ->
  run_io (slice_append tag s v) w0
    = ORet (mkSliceH (sh_base s) (sh_off s) (PrimInt63.add (sh_len s) 1) (sh_cap s) tag)
           (ref_upd (sh_cell s (sh_len s)) v w0).
Proof.
  intros A tag len cap v w Hlt s w0 Hmk.
  (* the handle from make_lc has sh_len = len, sh_cap = cap, so len < cap ⇒ in place *)
  unfold slice_make_lc, run_io in Hmk. injection Hmk as Hs _. subst s.
  apply slice_append_incap. exact Hlt.
Qed.

(* Element [i]'s cell is [sh_start s + i] (= [sh_loc s i] by [add_assoc]); the
   clear/copy ranges are the interval [[sh_start s, sh_start s + len)]. *)
Definition sh_start {A} (s : SliceH A) : int := PrimInt63.add (sh_base s) (sh_off s).

(** [clear(s)] (Go 1.21, Phase B3c): zero [s]'s [len] elements.  A single declarative
    heap update — the cells in [s]'s range map to the zero value, the rest unchanged. *)
Definition slice_clear_h {A} (tag : GoTypeTag A) (s : SliceH A) : IO unit :=
  fun w => ORet tt
    (mkWorld (fun k => if (PrimInt63.leb (sh_start s) k
                           && PrimInt63.ltb k (PrimInt63.add (sh_start s) (sh_len s)))%bool
                       then Some (existT _ A (tag, zero_val tag))
                       else w_refs w k)
             (w_chans w) (w_maps w) (w_next w)).

(** [copy(dst, src)] (Phase B3c): copy [min(len dst, len src)] elements [src → dst],
    return the count.  A single declarative heap update — each [dst] cell in range takes
    the corresponding [src] value ([src]'s cell at the same relative index). *)
Definition slice_copy {A} (tag : GoTypeTag A) (dst src : SliceH A) : IO int :=
  fun w => let n := if PrimInt63.leb (sh_len dst) (sh_len src) then sh_len dst else sh_len src in
           ORet n
    (mkWorld (fun k => if (PrimInt63.leb (sh_start dst) k
                           && PrimInt63.ltb k (PrimInt63.add (sh_start dst) n))%bool
                       then Some (existT _ A
                              (tag, ref_sel (mkRef (PrimInt63.add (sh_start src)
                                                      (PrimInt63.sub k (sh_start dst)))
                                                   (sh_tag src)) w))
                       else w_refs w k)
             (w_chans w) (w_maps w) (w_next w)).

(** ---- Heap-backed STRUCTS as field-cell bundles (Phase Bs) ----

    A user struct cannot be a single [w_refs] cell: [GoTypeTag] has no struct
    constructor (and [tag_eq]'s decidable type-equality cannot produce the [A = B] proof
    for opaque struct types — the wall).  The principled model: a struct value in storage
    is a BUNDLE of scalar FIELD-CELLS — field [k] lives at cell [base + k], tagged with
    its OWN scalar [GoTypeTag] — so only the scalar field tags are ever needed,
    sidestepping the wall (the same consecutive-cell shape as [SliceH], but the fields
    are HETEROGENEOUS).  A struct POINTER is just the [base] location.  This is the
    SUBSTRATE that [B2] (pointer receivers) needs; it ALSO unblocks structs in
    [any]/channels/maps (all blocked by the same wall).  Every law is inherited from
    [ref_sel_upd_same] — NO new heap, NO new axiom. *)
Record HStruct := mkHStruct { hs_base : int }.
Definition hfield_cell {A} (h : HStruct) (k : int) (tag : GoTypeTag A) : Ref A :=
  mkRef (PrimInt63.add (hs_base h) k) tag.
Definition hfield_get {A} (h : HStruct) (k : int) (tag : GoTypeTag A) : IO A :=
  fun w => ORet (ref_sel (hfield_cell h k tag) w) w.
Definition hfield_set {A} (h : HStruct) (k : int) (tag : GoTypeTag A) (v : A) : IO unit :=
  fun w => ORet tt (ref_upd (hfield_cell h k tag) v w).
Lemma run_hfield_get : forall {A} (h : HStruct) (k : int) (tag : GoTypeTag A) (w : World),
  run_io (hfield_get h k tag) w = ORet (ref_sel (hfield_cell h k tag) w) w.
Proof. reflexivity. Qed.
Lemma run_hfield_set : forall {A} (h : HStruct) (k : int) (tag : GoTypeTag A) (v : A) (w : World),
  run_io (hfield_set h k tag v) w = ORet tt (ref_upd (hfield_cell h k tag) v w).
Proof. reflexivity. Qed.

(** A [ref_sel] at a DIFFERENT location is unaffected by a [ref_upd] — the foundation
    for field INDEPENDENCE (writing one field leaves the others alone). *)
Lemma ref_sel_upd_diff : forall {A B} (r : Ref A) (r' : Ref B) (v : A) (w : World),
  r_loc r <> r_loc r' -> ref_sel r' (ref_upd r v w) = ref_sel r' w.
Proof.
  intros A B r r' v w Hne. unfold ref_sel, ref_upd. cbn.
  destruct (PrimInt63.eqb (r_loc r') (r_loc r)) eqn:E; [|reflexivity].
  apply Uint63.eqb_spec in E. congruence.
Qed.

(** CROSS-RESOURCE separation: the [World]'s ref-heap and channel-heap are INDEPENDENT components
    ([w_refs] vs [w_chans]), so a CHANNEL op leaves every ref untouched and a REF op leaves every
    channel untouched.  These let a single [run_io] world match BOTH the calculus's channel AND heap
    state at once (the combined state refinement). *)
Lemma ref_sel_chan_write_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) buf cl (r : Ref B) (w : World),
  ref_sel r (chan_write tag ch buf cl w) = ref_sel r w.
Proof. intros. unfold ref_sel, chan_write. reflexivity. Qed.

Lemma ref_sel_chan_send_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (v : A) (r : Ref B) (w : World),
  ref_sel r (chan_send_upd tag ch v w) = ref_sel r w.
Proof. intros. unfold chan_send_upd. apply ref_sel_chan_write_frame. Qed.

Lemma ref_sel_chan_recv_upd : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (w : World),
  ref_sel r (chan_recv_upd tag ch w) = ref_sel r w.
Proof. intros. unfold chan_recv_upd. apply ref_sel_chan_write_frame. Qed.

Lemma chan_buf_ref_upd_frame : forall {A B} (tag : GoTypeTag A) (ch : GoChan A) (r : Ref B) (v : B) (w : World),
  chan_buf tag ch (ref_upd r v w) = chan_buf tag ch w.
Proof. intros. unfold chan_buf, ref_upd. reflexivity. Qed.

(** Field read-after-write — a THEOREM: after [hfield_set h k tag v], reading field [k]
    returns [v] (from [ref_sel_upd_same]). *)
Lemma hfield_get_set_same : forall {A} (h : HStruct) (k : int) (tag : GoTypeTag A) (v : A),
  bind (hfield_set h k tag v) (fun _ => hfield_get h k tag) =
  bind (hfield_set h k tag v) (fun _ => ret v).
Proof.
  intros. apply run_io_inj. intro w.
  rewrite !run_bind, run_hfield_set. cbn.
  rewrite run_hfield_get, ref_sel_upd_same, run_ret. reflexivity.
Qed.

(** DIFFERENT fields are INDEPENDENT — writing field [k] does NOT change field [k']
    (distinct field CELLS), even when the fields have DIFFERENT types.  A THEOREM.
    (Stated on the field-cell LOCATIONS being distinct, which holds for distinct field
    indices [k ≠ k']; the index ⇒ location step is [add]-injectivity on [Uint63], a
    [to_Z] modular-cancellation — left as a routine follow-up, immediate by [vm_compute]
    for any concrete index pair.) *)
Lemma hfield_independent : forall {A B} (h : HStruct) (k k' : int)
    (ta : GoTypeTag A) (tb : GoTypeTag B) (v : A) (w : World),
  PrimInt63.add (hs_base h) k <> PrimInt63.add (hs_base h) k' ->
  ref_sel (hfield_cell h k' tb) (ref_upd (hfield_cell h k ta) v w)
    = ref_sel (hfield_cell h k' tb) w.
Proof. intros A B h k k' ta tb v w Hne. apply ref_sel_upd_diff. cbn. exact Hne. Qed.

(** Two pointers to the SAME struct (same [base]) see each other's field writes — the
    aliasing a [*T] receiver relies on.  A THEOREM. *)
Lemma hstruct_alias : forall {A} (h h' : HStruct) (k : int) (tag : GoTypeTag A) (v : A) (w : World),
  hs_base h = hs_base h' ->
  ref_sel (hfield_cell h k tag) (ref_upd (hfield_cell h' k tag) v w) = v.
Proof.
  intros A h h' k tag v w Hb. unfold hfield_cell. rewrite Hb.
  apply (ref_sel_upd_same (mkRef (PrimInt63.add (hs_base h') k) tag) v w).
Qed.

(** ---- Struct POINTERS (Phase Bs.2): a heap-backed struct ↔ Go [*R] ----

    A [*R] is the [base] of the struct's field-cell bundle (Bs.1) PLUS a [StructRep]
    — the per-record DATA (its field projections + constructor + the record eta law)
    that lets the generic ops DECOMPOSE a struct value into field cells and RECONSTRUCT
    it.  Coq has no generic record reflection, so [StructRep] is the one bit of
    per-struct data; it is DATA-only (the function fields are plain projections, NOT
    [GoTypeTag] — so it does NOT reintroduce the [tag_eq] wall).  [SPtr R] carries the
    [StructRep] in a field so the type parameter [R] survives extraction (the plugin
    needs it to emit [*R], the same trick [Ptr] uses with [p_tag]).  This is the model
    for a 2-field, [int64]-fielded struct; wider/heterogeneous reps generalise it.
    Lowers (Bs.2 lowering, separate): [SPtr R] → [*R], [sptr_new] → [&R{…}],
    [sptr_deref] → [*p], [sptr_assign] → [*p = R{…}], reusing the [Ptr] arms. *)
Record StructRep2 (R : Type) := mkSR2 {
  sr2_f0 : R -> GoI64 ;                                   (* field 0 projection *)
  sr2_f1 : R -> GoI64 ;                                   (* field 1 projection *)
  sr2_mk : GoI64 -> GoI64 -> R ;                          (* constructor *)
  sr2_eta : forall v, sr2_mk (sr2_f0 v) (sr2_f1 v) = v ;  (* the record eta law *)
}.
Arguments mkSR2 {R} _ _ _ _.
Arguments sr2_f0 {R} _ _.  Arguments sr2_f1 {R} _ _.
Arguments sr2_mk {R} _ _ _.  Arguments sr2_eta {R} _ _.

(** ---- STRUCT CHANNELS (send a NAMED 2-field struct over a channel) ----

    A struct channel is a [GoChan R] (tag-FREE phantom [R]).  A nominal [GoTypeTag R] is
    impossible — [tag_eq] cannot decide downstream nominal type equality — so the CELL instead
    stores the struct's FIELD TUPLE, tagged by the DECIDABLE [TProd TI64 TI64] (a product is
    canonical, so [tag_eq] recovers it).  The [StructRep2] marshals [R <-> (f0, f1)]; [sr2_eta]
    makes the round-trip FAITHFUL (proved below).  No nominal tag, no axiom.

    COHERENCE — closes a code-review hole.  Previously [struct_send2]/[struct_recv2] each took an
    INDEPENDENT [StructRep2 R]; two valid reps (e.g. normal vs swapped field order) each satisfy
    [sr2_eta] yet marshal differently, so sending with one and receiving with another would CHANGE
    the value (native [chan R] would not).  Fix: the rep is now bound to the TYPE by the [StructRep2Of]
    typeclass — [struct_send2]/[struct_recv2] both resolve THE canonical [the_struct_rep2 R], so a
    mismatched-rep round-trip is UNREPRESENTABLE (there is no explicit rep argument to disagree on),
    exactly as a Go [chan R] marshals [R] one fixed way.

    *(Extraction of the idiomatic native [chan R] / [ch <- p] / [<-ch] is the next slice: Coq's
    [prod] is the multi-return tuple, so emitting it as a Go struct needs dedicated plugin work;
    this slice lands the MODEL + the correctness theorem.)* *)
Class StructRep2Of (R : Type) : Type := the_struct_rep2 : StructRep2 R.
Arguments the_struct_rep2 R {_}.
Definition struct_make2 {R} (n : int) : IO (GoChan R) :=
  bind (make_chan_buf (TProd TI64 TI64) n) (fun ch => ret (MkChan (ch_loc ch))).
Definition struct_send2 {R} `{StructRep2Of R} (ch : GoChan R) (v : R) : IO unit :=
  send (TProd TI64 TI64) (MkChan (ch_loc ch))
       (sr2_f0 (the_struct_rep2 R) v, sr2_f1 (the_struct_rep2 R) v).
Definition struct_recv2 {R} `{StructRep2Of R} (ch : GoChan R) : IO R :=
  bind (recv (TProd TI64 TI64) (MkChan (ch_loc ch)))
       (fun p => ret (sr2_mk (the_struct_rep2 R) (fst p) (snd p))).

(** CORRECTNESS — round-trip faithfulness.  On an OPEN, EMPTY channel, [struct_send2] then
    [struct_recv2] recovers the struct EXACTLY: the field-tuple marshalling is lossless, by
    [sr2_eta] of the channel's CANONICAL rep (send and recv share it — no rep to mismatch).  This
    is the acceptance test at the model level (a struct survives a channel round-trip intact). *)
Theorem struct_chan_roundtrip2 :
  forall {R} `{StructRep2Of R} (ch : GoChan R) (v : R) (w : World),
    @chan_closed (GoI64 * GoI64)%type (MkChan (ch_loc ch)) w = false ->
    chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch)) w = nil ->
    exists w', run_io (bind (struct_send2 ch v)
                            (fun _ => struct_recv2 ch)) w = ORet v w'.
Proof.
  intros R Hrep ch v w Hopen Hempty.
  unfold struct_send2, struct_recv2.
  set (rep := the_struct_rep2 R).
  rewrite run_bind.
  rewrite (run_send (TProd TI64 TI64) (MkChan (ch_loc ch)) (sr2_f0 rep v, sr2_f1 rep v) w Hopen).
  rewrite run_bind.
  assert (Hbuf1 : chan_buf (TProd TI64 TI64) (MkChan (ch_loc ch))
            (chan_send_upd (TProd TI64 TI64) (MkChan (ch_loc ch)) (sr2_f0 rep v, sr2_f1 rep v) w)
          = (sr2_f0 rep v, sr2_f1 rep v) :: nil)
    by (rewrite chan_buf_send, Hempty; reflexivity).
  rewrite (run_recv (TProd TI64 TI64) (MkChan (ch_loc ch))
                    (sr2_f0 rep v, sr2_f1 rep v) nil _ Hbuf1).
  rewrite run_ret. cbn [fst snd]. rewrite (sr2_eta rep v).
  eexists; reflexivity.
Qed.

(** Why coherence MATTERS — a concrete demo on the 2-field "struct" [GoI64 * GoI64].  Its canonical
    rep is the identity projections; a SWAPPED rep ([snd]/[fst]) also satisfies [sr2_eta] yet
    marshals an ASYMMETRIC value to a DIFFERENT tuple.  So mixing reps across send/recv would corrupt
    the value — which the type-bound [the_struct_rep2] now makes impossible. *)
#[local] Instance StructRep2Of_prod : StructRep2Of (GoI64 * GoI64) :=
  mkSR2 fst snd (fun a b => (a, b)) (fun v => match v with (a, b) => eq_refl end).
Definition sr2_swapped : StructRep2 (GoI64 * GoI64) :=
  mkSR2 snd fst (fun a b => (b, a)) (fun v => match v with (a, b) => eq_refl end).
Example struct_reps_disagree :
  sr2_f0 (the_struct_rep2 (GoI64 * GoI64)) (i64_lit 1 eq_refl, i64_lit 2 eq_refl)
    <> sr2_f0 sr2_swapped (i64_lit 1 eq_refl, i64_lit 2 eq_refl).
Proof. cbn. intro H. apply (f_equal i64raw) in H. cbn in H. discriminate. Qed.

Record SPtr (R : Type) := mkSPtr { sp_base : int ; sp_rep : StructRep2 R }.
Arguments mkSPtr {R} _ _.
Arguments sp_base {R} _.  Arguments sp_rep {R} _.

Definition sptr_hs {R} (p : SPtr R) : HStruct := mkHStruct (sp_base p).

(** [sptr_new rep v] — Go [p := &R{…}]: allocate a FRESH base, write each field cell
    from [v]'s projections, bump the allocator by the field count (2), return the
    pointer carrying [rep]. *)
Definition sptr_new {R} (rep : StructRep2 R) (v : R) : IO (SPtr R) :=
  fun w =>
    let l := w_next w in
    let p := mkSPtr l rep in
    let wa := mkWorld (w_refs w) (w_chans w) (w_maps w) (PrimInt63.add l 2) in  (* bump allocator *)
    let w0 := ref_upd (hfield_cell (sptr_hs p) 0%uint63 TI64) (sr2_f0 rep v) wa in
    let w1 := ref_upd (hfield_cell (sptr_hs p) 1%uint63 TI64) (sr2_f1 rep v) w0 in
    ORet p w1.

(** [sptr_deref p] — Go [*p]: read both field cells, RECONSTRUCT the struct via [rep]. *)
Definition sptr_deref {R} (p : SPtr R) : IO R :=
  bind (hfield_get (sptr_hs p) 0%uint63 TI64) (fun a =>
  bind (hfield_get (sptr_hs p) 1%uint63 TI64) (fun b =>
  ret (sr2_mk (sp_rep p) a b))).

(** [sptr_assign p v] — Go [*p = R{…}]: write both field cells from [v] (whole-struct
    write through the pointer; mutation is observed by any handle to the same base). *)
Definition sptr_assign {R} (p : SPtr R) (v : R) : IO unit :=
  bind (hfield_set (sptr_hs p) 0%uint63 TI64 (sr2_f0 (sp_rep p) v)) (fun _ =>
        hfield_set (sptr_hs p) 1%uint63 TI64 (sr2_f1 (sp_rep p) v)).

(** FIELD-level access through the pointer — Go [p.Field] / [p.Field = v] (the idiomatic
    form the Bs.2 lowering targets).  [idx] selects the field cell, [proj] names it (for
    the plugin's [proj → field-name] map) and SPECIFIES the read (it equals [proj] of the
    pointee).  Built directly on the field-cell substrate. *)
Definition sptr_get_field {R F} (p : SPtr R) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) : IO F :=
  hfield_get (sptr_hs p) idx ftag.
Definition sptr_set_field {R F} (p : SPtr R) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) (v : F) : IO unit :=
  hfield_set (sptr_hs p) idx ftag v.

(** Field read-after-write THROUGH the pointer — a THEOREM: after [sptr_set_field p idx
    proj ftag v], reading the SAME field returns [v].  The mutation-through-pointer that
    a [*T] receiver relies on, reduced directly to [hfield_get_set_same]. *)
Lemma sptr_field_get_set : forall {R F} (p : SPtr R) (idx : int) (proj : R -> F)
    (ftag : GoTypeTag F) (v : F),
  bind (sptr_set_field p idx proj ftag v) (fun _ => sptr_get_field p idx proj ftag) =
  bind (sptr_set_field p idx proj ftag v) (fun _ => ret v).
Proof.
  intros. unfold sptr_set_field, sptr_get_field. apply hfield_get_set_same.
Qed.

(** Two handles to the SAME pointer (same base) see each other's field writes — the
    ALIASING a [*T] receiver relies on, reduced to [hstruct_alias].  (The whole-struct
    [sptr_deref]-after-[sptr_assign] round-trip — reassembling via [sr2_eta] across both
    field cells — follows from this + field independence; deferred, fiddlier [run_bind]
    sequencing.) *)
Lemma sptr_field_alias : forall {R F} (p q : SPtr R) (idx : int)
    (ftag : GoTypeTag F) (v : F) (w : World),
  sp_base p = sp_base q ->
  ref_sel (hfield_cell (sptr_hs p) idx ftag) (ref_upd (hfield_cell (sptr_hs q) idx ftag) v w) = v.
Proof.
  intros R F p q idx ftag v w Hb. apply hstruct_alias. unfold sptr_hs. cbn. exact Hb.
Qed.

(** ---- N-FIELD struct pointers (THREE fields) ----  The same field-cell substrate,
    generalised from [StructRep2]/[SPtr] to a third field.  Field access ([sptr3_get_field]/
    [sptr3_set_field]) and the read-after-write THEOREM are the SAME generic [hfield] ops
    (so no new heap reasoning) — only the rep and the allocation widen by one field.  A
    function whose first param is [SPtr3 R] becomes a pointer-receiver method on a 3-field
    [*R], exactly like the 2-field case. *)
Record StructRep3 (R : Type) := mkSR3 {
  sr3_f0 : R -> GoI64 ; sr3_f1 : R -> GoI64 ; sr3_f2 : R -> GoI64 ;
  sr3_mk : GoI64 -> GoI64 -> GoI64 -> R ;
  sr3_eta : forall v, sr3_mk (sr3_f0 v) (sr3_f1 v) (sr3_f2 v) = v ;
}.
Arguments mkSR3 {R} _ _ _ _ _.
Arguments sr3_f0 {R} _ _.  Arguments sr3_f1 {R} _ _.  Arguments sr3_f2 {R} _ _.
Arguments sr3_mk {R} _ _ _ _.
Record SPtr3 (R : Type) := mkSPtr3 { sp3_base : int ; sp3_rep : StructRep3 R }.
Arguments mkSPtr3 {R} _ _.
Arguments sp3_base {R} _.  Arguments sp3_rep {R} _.
Definition sptr3_hs {R} (p : SPtr3 R) : HStruct := mkHStruct (sp3_base p).
Definition sptr3_new {R} (rep : StructRep3 R) (v : R) : IO (SPtr3 R) :=
  fun w =>
    let l := w_next w in
    let p := mkSPtr3 l rep in
    let wa := mkWorld (w_refs w) (w_chans w) (w_maps w) (PrimInt63.add l 3) in  (* bump by 3 *)
    let w0 := ref_upd (hfield_cell (sptr3_hs p) 0%uint63 TI64) (sr3_f0 rep v) wa in
    let w1 := ref_upd (hfield_cell (sptr3_hs p) 1%uint63 TI64) (sr3_f1 rep v) w0 in
    let w2 := ref_upd (hfield_cell (sptr3_hs p) 2%uint63 TI64) (sr3_f2 rep v) w1 in
    ORet p w2.
Definition sptr3_get_field {R F} (p : SPtr3 R) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) : IO F :=
  hfield_get (sptr3_hs p) idx ftag.
Definition sptr3_set_field {R F} (p : SPtr3 R) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) (v : F) : IO unit :=
  hfield_set (sptr3_hs p) idx ftag v.
Lemma sptr3_field_get_set : forall {R F} (p : SPtr3 R) (idx : int) (proj : R -> F)
    (ftag : GoTypeTag F) (v : F),
  bind (sptr3_set_field p idx proj ftag v) (fun _ => sptr3_get_field p idx proj ftag) =
  bind (sptr3_set_field p idx proj ftag v) (fun _ => ret v).
Proof. intros. unfold sptr3_set_field, sptr3_get_field. apply hfield_get_set_same. Qed.

(** ---- HETEROGENEOUS 2-field struct pointer ([SPtrH R A B]) ----
    The common real-Go case: a pointer to a struct whose fields have DIFFERENT types
    (e.g. [*struct{ N int64; B bool }]).  The field-cell heap ([hfield_cell]) is already
    GENERIC over the field type (it takes a [GoTypeTag]), so this only generalises the rep
    to carry per-field types [A], [B] and their tags; the field read/write THEOREM is again
    the 2-field/[hfield_get_set_same] proof verbatim.  Lowers exactly like [SPtr]/[SPtr3]
    ([*R], [&R{…}], [p.Field]); the only plugin change is taking the FIRST type arg of the
    3-arg [SPtrH R A B] (vs [SPtr R]'s single arg). *)
Record StructRep2H (R A B : Type) := mkSR2H {
  sr2h_f0 : R -> A ;                                       (* field 0 projection (type A) *)
  sr2h_f1 : R -> B ;                                       (* field 1 projection (type B) *)
  sr2h_ta : GoTypeTag A ;                                  (* field 0 type tag *)
  sr2h_tb : GoTypeTag B ;                                  (* field 1 type tag *)
  sr2h_mk : A -> B -> R ;                                  (* constructor *)
  sr2h_eta : forall v, sr2h_mk (sr2h_f0 v) (sr2h_f1 v) = v ;
}.
Arguments mkSR2H {R A B} _ _ _ _ _ _.
Arguments sr2h_f0 {R A B} _ _.  Arguments sr2h_f1 {R A B} _ _.
Arguments sr2h_ta {R A B} _.    Arguments sr2h_tb {R A B} _.
Arguments sr2h_mk {R A B} _ _ _.  Arguments sr2h_eta {R A B} _ _.

Record SPtrH (R A B : Type) := mkSPtrH { sph_base : int ; sph_rep : StructRep2H R A B }.
Arguments mkSPtrH {R A B} _ _.
Arguments sph_base {R A B} _.  Arguments sph_rep {R A B} _.

Definition sptrh_hs {R A B} (p : SPtrH R A B) : HStruct := mkHStruct (sph_base p).

(** [sptrh_new rep v] — Go [p := &R{…}]: write field 0 at tag [A], field 1 at tag [B]. *)
Definition sptrh_new {R A B} (rep : StructRep2H R A B) (v : R) : IO (SPtrH R A B) :=
  fun w =>
    let l := w_next w in
    let p := mkSPtrH l rep in
    let wa := mkWorld (w_refs w) (w_chans w) (w_maps w) (PrimInt63.add l 2) in
    let w0 := ref_upd (hfield_cell (sptrh_hs p) 0%uint63 (sr2h_ta rep)) (sr2h_f0 rep v) wa in
    let w1 := ref_upd (hfield_cell (sptrh_hs p) 1%uint63 (sr2h_tb rep)) (sr2h_f1 rep v) w0 in
    ORet p w1.

Definition sptrh_get_field {R A B F} (p : SPtrH R A B) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) : IO F :=
  hfield_get (sptrh_hs p) idx ftag.
Definition sptrh_set_field {R A B F} (p : SPtrH R A B) (idx : int) (proj : R -> F) (ftag : GoTypeTag F) (v : F) : IO unit :=
  hfield_set (sptrh_hs p) idx ftag v.

Lemma sptrh_field_get_set : forall {R A B F} (p : SPtrH R A B) (idx : int) (proj : R -> F)
    (ftag : GoTypeTag F) (v : F),
  bind (sptrh_set_field p idx proj ftag v) (fun _ => sptrh_get_field p idx proj ftag) =
  bind (sptrh_set_field p idx proj ftag v) (fun _ => ret v).
Proof. intros. unfold sptrh_set_field, sptrh_get_field. apply hfield_get_set_same. Qed.

(** WHOLE-STRUCT deref-after-assign — a THEOREM: after [sptr_assign p v], [sptr_deref p]
    reassembles [v].  Field 0 survives the field-1 write (distinct cells, [ref_sel_upd_diff]),
    field 1 read sees its write ([ref_sel_upd_same]), and [sr2_eta] rebuilds [v].  The
    field-cell distinctness ([base+0 ≠ base+1]) is the same hypothesis [hfield_independent]
    takes — true for every base, immediate by [vm_compute] for any concrete pointer.
    ([ref_sel]/[ref_upd]/[hfield_cell] are kept opaque so [cbn] reduces only the monadic
    [match]/[bind] structure, leaving the heap terms intact for the final rewrites.) *)
Local Opaque ref_sel ref_upd hfield_cell.
Lemma sptr_deref_assign : forall {R} (p : SPtr R) (v : R),
  r_loc (hfield_cell (sptr_hs p) 0%uint63 TI64) <> r_loc (hfield_cell (sptr_hs p) 1%uint63 TI64) ->
  bind (sptr_assign p v) (fun _ => sptr_deref p) =
  bind (sptr_assign p v) (fun _ => ret v).
Proof.
  intros R p v Hne. apply run_io_inj. intro w.
  unfold sptr_assign, sptr_deref.
  repeat (rewrite ?run_bind, ?run_hfield_set, ?run_hfield_get, ?run_ret; cbn).
  rewrite (ref_sel_upd_diff (hfield_cell (sptr_hs p) 1%uint63 TI64)
                            (hfield_cell (sptr_hs p) 0%uint63 TI64))
    by (apply not_eq_sym; exact Hne).
  rewrite !ref_sel_upd_same.
  rewrite (sr2_eta (sp_rep p) v). reflexivity.
Qed.
Local Transparent ref_sel ref_upd hfield_cell.

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

(** ---- [range] over a string (Go spec "For statements: For range"): [for i, r := range s] ----
    Go ranges a STRING by UTF-8 code point: [i] is the BYTE offset of each code point's first
    byte, [r] the decoded rune.  Modeled faithfully on the rune view: [str_to_runes_w] decodes
    each rune WITH the number of source bytes it consumed, and the byte offsets are the running
    prefix sums of those CONSUMED widths — exactly Go's string-range index, even for invalid
    UTF-8 (machine-checked by [str_range_offsets] / [str_range_invalid_offsets] in main.v).
    ([rune_width] — utf8.RuneLen, a rune's ENCODED length — is a separate utility.)  [str_range] lowers
    to the NATIVE two-variable [for i, r := range s]; the [for_each_pairs]/[runes_with_offsets]
    model is proof-only (recognized by name, decl suppressed), so the emitted Go is the
    idiomatic range loop — never a [[]rune] materialisation.  The index is the Go [int] index
    type ([Sint63], → the loop's [int] variable). *)
Definition rune_width (r : GoI32) : int :=
  let c := i32raw r in
  if PrimInt63.ltb c 128%uint63   then 1%uint63    (* 1-byte (ASCII) *)
  else if PrimInt63.ltb c 2048%uint63  then 2%uint63    (* 2-byte *)
  else if PrimInt63.ltb c 65536%uint63 then 3%uint63    (* 3-byte *)
  else 4%uint63.                                          (* 4-byte *)
(** Byte offsets are the running prefix sums of the CONSUMED SOURCE widths (the [int] tag from
    [str_to_runes_w]), so an invalid byte advances the offset by ONE — matching Go's range even
    for invalid UTF-8 (review #6 P1 #9).  Re-encoding the decoded rune (via [rune_width]) would
    OVER-count: U+FFFD is 3 bytes encoded but a malformed byte consumes only 1. *)
Fixpoint runes_with_offsets (off : int) (rs : list (GoI32 * int)) : list (int * GoI32) :=
  match rs with
  | nil              => nil
  | cons (r, w) rest => cons (off, r) (runes_with_offsets (PrimInt63.add off w) rest)
  end.
Fixpoint for_each_pairs {A B : Type} (xs : list (A * B)) (body : A -> B -> IO unit) : IO unit :=
  match xs with
  | nil              => ret tt
  | cons (a, b) rest => bind (body a b) (fun _ => for_each_pairs rest body)
  end.
Definition str_range (s : GoString) (body : int -> GoI32 -> IO unit) : IO unit :=
  for_each_pairs (runes_with_offsets 0%uint63 (str_to_runes_w s)) body.

(** ---- Indexed [range] over a slice (Go spec "For statements: For range"): [for i, x := range xs] ----
    [i] is the element INDEX (0, 1, 2, …), [x] the element — the indexed counterpart of
    [for_each] (which discards the index).  The index is the Go [int] index type ([Sint63]).
    Lowers to the native two-variable [for i, x := range xs]; the accumulator model below is
    proof-only (recognized by name, decl suppressed). *)
Fixpoint for_each_idx_from {A : Type} (i : int) (xs : GoSlice A) (body : int -> A -> IO unit) : IO unit :=
  match xs with
  | nil         => ret tt
  | cons x rest => bind (body i x) (fun _ => for_each_idx_from (PrimInt63.add i 1%uint63) rest body)
  end.
Definition for_each_idx {A : Type} (xs : GoSlice A) (body : int -> A -> IO unit) : IO unit :=
  for_each_idx_from 0%uint63 xs body.

(** ---- Integer [range] (Go 1.22, spec "For statements: For range" over an integer): [for i := range n] ----
    Produces [i = 0, 1, …, n-1] (and runs zero times when [n = 0], exactly Go's rule).
    The bound [n] is the iteration COUNT (a [nat] — non-negative, and the structural-recursion
    fuel, so termination is by construction with no carrier conversion); the produced index
    [i] is the Go [int] index type ([Sint63]).  Recognized by name + decl suppressed, so the
    lowering is the native [for i := range n] (the [nat] count renders as the bound). *)
Fixpoint int_range_aux (i : int) (n : nat) (body : int -> IO unit) : IO unit :=
  match n with
  | O    => ret tt
  | S f  => bind (body i) (fun _ => int_range_aux (PrimInt63.add i 1%uint63) f body)
  end.
Definition int_range (n : nat) (body : int -> IO unit) : IO unit :=
  int_range_aux 0%uint63 n body.

(** [slice_fold xs init step] is a pure left fold: it threads an accumulator
    through the slice, [step]ping it with each element.  A total Fixpoint, so
    its unfolding is provable:
      [slice_fold nil init step = init]
      [slice_fold (x :: rest) init step = slice_fold rest (step init x) step]
    The plugin lowers a [let acc := slice_fold xs init step in …] to an
    accumulator loop:
      [acc := init; for _, x := range xs { acc = step acc x }; …]
    so e.g. summing a slice is a real Go [for] loop, and "the running sum does
    not overflow" is provable on the model (see [i64_add_no_overflow_exact] in main.v). *)
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

(** [Sess i j A] is the FORGE-PROOF session type (review #3 R9 — migration of the
    user-chosen deeper fix into the extracted layer, 2026-06-22): an INDUCTIVE
    whose only builders are the disciplined ops below.  There is NO [MkSess]-style
    constructor wrapping an arbitrary [IO A] at any index, so the protocol index
    CANNOT be detached from the operations — a forged "[… : Sess (PSend A P) P unit]
    that sends nothing" is now UNTYPABLE (the old record's public [MkSess] could
    build it; see the [Fail] tests in main.v).  The indices are rigid inductive
    indices (not a convertible [IO A] alias), so double-use, wrong order / direction
    / payload, AND incomplete protocols ([j <> PEnd]) are all TYPE ERRORS.  [Sess]
    erases in extraction — lowered by OPERATION NAME (channel passing), never
    materialised as a Go value — so the emitted Go is unchanged by this migration.
    Its full safety+liveness theory is in concurrency.v (bricks 1–5: soundness,
    communication safety, deadlock-freedom, termination / determinism, run-trace
    coherence) — proved DIRECTLY about THIS type ([PSess]/[PS…] there are aliases
    for [Sess]/[S…], so the theorems are literally about the extracted type). *)
Inductive Sess : Proto -> Proto -> Type -> Type :=
  | SRet  : forall {P : Proto} {A : Type}, A -> Sess P P A
  | SSend : forall {A : Type} {P : Proto}, A -> Sess (PSend A P) P unit
  | SRecv : forall {A : Type} {P : Proto}, GoTypeTag A -> Sess (PRecv A P) P A
  | SLift : forall {P : Proto} {A : Type}, IO A -> Sess P P A
  | SBind : forall {P Q R : Proto} {A B : Type},
              Sess P Q A -> (A -> Sess Q R B) -> Sess P R B.

(** Pure value; protocol state unchanged.  Lowers like [ret]. *)
Definition sret {P : Proto} {A : Type} (x : A) : Sess P P A := SRet x.

(** Sequence: [m] advances [i→j], then [k a] advances [j→k].  Lowers like
    [bind] (sequential Go statements). *)
Definition sbind {P Q R : Proto} {A B : Type}
  (m : Sess P Q A) (k : A -> Sess Q R B) : Sess P R B := SBind m k.

(** Send: consumes the head [PSend A] step.  No endpoint argument — the channel
    is implicit, supplied by the enclosing [run_session].
    Lowers to [_sess_ch <- any(v)]. *)
Definition ssend {A : Type} {P : Proto} (v : A) : Sess (PSend A P) P unit := SSend v.

(** Receive: consumes the head [PRecv A] step, yielding the received value.
    Lowers to [_r := <-_sess_ch; _r.(T)]. *)
Definition srecv {A : Type} {P : Proto} (tag : GoTypeTag A) : Sess (PRecv A P) P A := SRecv tag.

(** Lift an [IO] action into a session at any protocol state (consumes no
    protocol step) — e.g. to print a received value.  Lowers to the IO body. *)
Definition slift {P : Proto} {A : Type} (m : IO A) : Sess P P A := SLift m.

(** [sret]…[run_session] are already in main.v's [Extraction NoInline] list, so they
    stay named refs (NOT inlined to their constructors) and the plugin's by-operation-
    name session lowering fires exactly as before — the emitted Go is unchanged. *)

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


