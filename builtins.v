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
Axiom World : Type.

Definition GoAny : Type := {T : Type & T}.
Notation any x := (@existT Type (fun T : Type => T) _ x).

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
Record GoU8 := MkU8 { u8raw : int }.
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
Record GoI8 := MkI8 { i8raw : int }.
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
Record GoU16 := MkU16 { u16raw : int }.
Definition u16_lit (x : int) (_ : (x <? 65536)%uint63 = true) : GoU16 := MkU16 x.
Definition u16_add (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.add (u16raw a) (u16raw b)) 65535).
Definition u16_sub (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.sub (u16raw a) (u16raw b)) 65535).
Definition u16_mul (a b : GoU16) : GoU16 := MkU16 (PrimInt63.land (PrimInt63.mul (u16raw a) (u16raw b)) 65535).
Definition u16_eqb (a b : GoU16) : bool := PrimInt63.eqb (u16raw a) (u16raw b).
Definition u16_ltb (a b : GoU16) : bool := PrimInt63.ltb (u16raw a) (u16raw b).
Definition u16_leb (a b : GoU16) : bool := PrimInt63.leb (u16raw a) (u16raw b).

Record GoI16 := MkI16 { i16raw : int }.
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

    NOTABLE OMISSION — [u32_mul]/[i32_mul] are NOT defined.  A 32-bit product can
    reach [(2^32-1)^2 ≈ 2^64], which EXCEEDS the 63-bit carrier — so a masked-
    product model would SILENTLY WRAP at [2^63] and give the wrong answer.  Per the
    fail-loud policy we omit it (the plugin already aborts a [>30]-bit fixed-width
    multiply); 32-bit multiply needs the Z-based wide-int model. *)
Record GoU32 := MkU32 { u32raw : int }.
Definition u32_lit (x : int) (_ : (x <? 4294967296)%uint63 = true) : GoU32 := MkU32 x.
Definition u32_add (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.add (u32raw a) (u32raw b)) 4294967295).
Definition u32_sub (a b : GoU32) : GoU32 := MkU32 (PrimInt63.land (PrimInt63.sub (u32raw a) (u32raw b)) 4294967295).
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

Record GoI32 := MkI32 { i32raw : int }.
Definition i32_norm (x : int) : int :=
  PrimInt63.sub (PrimInt63.lxor (PrimInt63.land x 4294967295) 2147483648) 2147483648.
Definition i32_lit (x : int) (_ : (Sint63.leb (-2147483648)%sint63 x && Sint63.ltb x 2147483648)%bool = true) : GoI32 := MkI32 x.
Definition i32_add (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.add (i32raw a) (i32raw b))).
Definition i32_sub (a b : GoI32) : GoI32 := MkI32 (i32_norm (PrimInt63.sub (i32raw a) (i32raw b))).
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

(** [clear(m)] (Go 1.21): remove ALL entries — like [map_delete] but for every
    key.  Grounded in the heap ([map_clear_upd] empties the map; [map_sel_clear]
    says every key reads [None] afterward), so GET-AFTER-CLEAR is a THEOREM. *)
Axiom map_clear     : forall {K V : Type}, GoMap K V -> IO unit.
Axiom map_clear_upd : forall {K V : Type}, GoMap K V -> World -> World.
Axiom run_map_clear : forall {K V} (m : GoMap K V) (w : World),
  run_io (map_clear m) w = ORet tt (map_clear_upd m w).
Axiom map_sel_clear : forall {K V} (k : K) (m : GoMap K V) (w : World),
  map_sel k m (map_clear_upd m w) = None.

Lemma map_get_clear : forall {K V} (k : K) (m : GoMap K V),
  bind (map_clear m) (fun _ => map_get_opt k m) =
  bind (map_clear m) (fun _ => ret (@None V)).
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

(** ---- select (Go spec "Select statements") ----

    [select] chooses ONE among several ready communications; "if one or more of
    the communications can proceed, a single one that can proceed is chosen via a
    uniform pseudo-random selection"; a [default] case runs when none are ready;
    with no default and nothing ready, the select BLOCKS.

    [select_recv2 ta ch1 k1 tb ch2 k2] receives from whichever of [ch1]/[ch2] is
    ready and runs the matching continuation; it lowers to a faithful Go
    [select { case x := <-ch1: k1; case y := <-ch2: k2 }].
    [select_recv_default ta ch1 k1 d] is the non-blocking form: receive-and-[k1]
    if [ch1] is ready, else run [d] — Go's [select { case … : k1; default: d }].

    CPS like [recv_ok] (no tuple/sum extraction needed).  The LOWERING is faithful
    Go.  The denotational CHOICE / BLOCKING semantics (which ready case runs, the
    pseudo-random fairness, blocking when none ready) is idealised away for now —
    exactly like [recv]'s blocking and divergence (Tier 5 #14: needs the
    non-terminating / scheduler model).  So [select] is grounded at the lowering
    level today; its choice semantics is the tracked incremental frontier. *)
Axiom select_recv2 : forall {A B C : Type},
  GoTypeTag A -> GoChan A -> (A -> IO C) ->
  GoTypeTag B -> GoChan B -> (B -> IO C) -> IO C.
Axiom select_recv_default : forall {A C : Type},
  GoTypeTag A -> GoChan A -> (A -> IO C) -> IO C -> IO C.

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

(** Channel SEPARATION (frame): a send/receive on one channel leaves every OTHER
    channel's buffer untouched.  This is the standard heap-separation property —
    distinct cells are independent — validated by the SAME per-channel FIFO-map heap
    model that validates [chan_buf_send]/[chan_buf_recv] (a [send_upd]/[recv_upd]
    rewrites only its own channel's slot).  It is what lets a MULTI-channel /
    MULTI-goroutine execution's state stay matched to the calculus: an operation on
    one channel does not perturb the others.  (Stated at one carrier type [A]; the
    keystone's channels are all [GoChan int].) *)
Axiom chan_buf_send_frame : forall {A} (ch ch' : GoChan A) (v : A) (w : World),
  ch <> ch' -> chan_buf ch' (chan_send_upd ch v w) = chan_buf ch' w.
Axiom chan_buf_recv_frame : forall {A} (ch ch' : GoChan A) (w : World),
  ch <> ch' -> chan_buf ch' (chan_recv_upd ch w) = chan_buf ch' w.

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

Axiom len    : forall {A : Type}, GoSlice A -> GoInt.
Axiom cap    : forall {A : Type}, GoSlice A -> GoInt.
Axiom append : forall {A : Type}, GoSlice A -> GoSlice A -> GoSlice A.

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
Axiom slice_of_list : forall {A : Type}, GoTypeTag A -> list A -> GoSlice A.

(** [make([]T, n)] — a fresh slice of [n] zero values (Go's [make] for slices).
    Modelled as [repeat (zero_val tag) n] (so [len] is [n], every element the zero
    value) — a freshly-allocated slice, hence no aliasing concern.  The plugin
    lowers it to Go [make([]T, n)] (element type from the tag, [n] the length).
    (The 3-arg [make([]T, len, cap)] and [copy] involve the backing-array /
    aliasing model — tracked separately, Tier 3 #8a.) *)
Definition slice_make {A : Type} (tag : GoTypeTag A) (n : nat) : GoSlice A :=
  List.repeat (zero_val tag) n.

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

Axiom str_at_ok : forall {B : Type},
  GoString -> int -> (GoByte -> bool -> IO B) -> IO B.

Fixpoint str_concat (a b : GoString) : GoString :=
  match a with
  | EmptyString   => b
  | String c rest => String c (str_concat rest b)
  end.

(** ---- Mutable local variables ----

    [Ref A] is a mutable cell holding an [A] — Go's mutable local variable.
    Pure [let]-binding is single-assignment and cannot express a value that
    *changes* (a loop counter, an accumulator updated in place); a [Ref] can.
    [ref_new v] declares the variable ([x := v]); [ref_get] reads it; [ref_set]
    assigns ([x = v]).  A local cell extracts to a plain Go variable;
    cross-function sharing (pointers, [*T]) is a later, separate step. *)
Axiom Ref     : Type -> Type.
(** A [Ref]'s value lives in the world: [ref_sel] reads it, [ref_upd] is the
    [ref_set] update.  These (and allocation [ref_new]) are the abstract heap
    STATE — the irreducible typed-cell core (a [Ref A] must extract to a Go
    variable of type [T], so it cannot become a concrete location without
    breaking extraction; see ZERO_AXIOMS_PLAN.md).  But the OPERATIONS and their
    [run_*] laws are now DEFINITIONS / THEOREMS, not axioms. *)
Axiom ref_sel : forall {A : Type}, Ref A -> World -> A.
Axiom ref_upd : forall {A : Type}, Ref A -> A -> World -> World.
Axiom ref_new : forall {A : Type}, A -> IO (Ref A).
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
Axiom run_session : forall {P : Proto},
  Sess P PEnd unit -> Sess (dual P) PEnd unit -> IO unit.
