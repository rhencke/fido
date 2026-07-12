(** ==================================================================================================
    GoSlice — the PURE-LIST slice and array model.  ★ALIASING CAVEAT (unmissable, by design):
    [GoSlice A = list A] is a VALUE model — [append] returns a new list — which is sound ONLY for
    single-goroutine sequential programs with NO aliasing of the underlying array.  Go's slices
    are reference types; the aliasing-capable representation is the heap-backed [SliceH] family
    (shared backing cells, [subslice]) living with the heap module.  Go's [cap] on value slices
    is INTENTIONALLY NOT MODELLED (implementation-defined after [append]); capacity-aware code
    uses [SliceH] with its explicit faithful capacity field.
    Includes: [len] + the agreement seal, [append], [slice_of_list], [slice_make], the panicking
    [slice_get] with its GATED two-sided bounds surface ([GoSlice.slice_get_bounds_surface]),
    the safe-by-construction [slice_at_ok], the fixed-size array family, and the structural
    iteration combinators [for_each]/[slice_fold].
    ================================================================================================ *)
Require Import Coq.Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.
From Fido Require Import GoPanic.

(* [len] counts elements, returning [GoInt] (lowered to Go [len] — body suppressed). *)
Fixpoint len {A} (xs : GoSlice A) : GoInt :=
  match xs with nil => intwrap 0 | _ :: r => intwrap (1 + intraw (len r)) end.
(** THE LEN AGREEMENT SEAL: on every REPRESENTABLE slice (length within int64 — every slice a real Go
    program can hold; Go caps slice length at max int) the Go-visible wrapped [len] IS the structural
    [List.length].  This certifies that the EMITTED [len(xs)] (a wrapped [GoInt]) agrees with the model's
    structural bounds on every representable state.  ⚠ It cannot hold unconditionally — [GoSlice A = list A] can
    represent a > 2^63-element list where [len] wraps — which is exactly why EVERY model bounds guard consults
    the STRUCTURAL [List.length] DIRECTLY: [slice_get] (the OOB-PANICKING index), the comma-ok safe index
    [slice_at_ok] / [arr_get_ok], and [arr_set]'s evidence — guard and payload share ONE authority on ALL
    states, with NO wrapped-[len] executable bad path anywhere in the family. *)
Lemma len_agrees_structural : forall {A} (xs : GoSlice A),
  (Z.of_nat (List.length xs) < 9223372036854775808)%Z ->
  intraw (len xs) = Z.of_nat (List.length xs).
Proof.
  induction xs as [| x r IH]; intro Hrep.
  - vm_compute. reflexivity.
  - cbn [List.length] in Hrep. rewrite Nat2Z.inj_succ in Hrep.
    cbn [len List.length intraw intwrap].
    rewrite IH by lia. rewrite Nat2Z.inj_succ, wrap64_small by lia. lia.
Qed.
(* a functional (value-)[GoSlice] [cap] is INTENTIONALLY NOT MODELLED: Go's [cap] after [append]
   is IMPLEMENTATION-DEFINED (append may over-allocate), so NO value-slice model can predict it
   faithfully — a PRINCIPLED, bounded NON-modelling.  Capacity-aware code uses the heap-backed
   [SliceH], whose capacity ([sh_cap]) is an explicit, faithful field of the value. *)
Definition append {A} (xs ys : GoSlice A) : GoSlice A := xs ++ ys.   (* GoSlice A = list A *)

(** Construct a typed Go slice from a Rocq list literal.
    The [GoTypeTag] witness makes the intended Go [[]T{v1, v2, ...}] with the
    correct element type instead of falling back to [append(nil, ...)]. *)
Definition slice_of_list {A} (_ : GoTypeTag A) (xs : list A) : GoSlice A := xs.

(** [make([]T, n)] — a fresh slice of [n] zero values (Go's [make] for slices).
    Modelled as [repeat (zero_val tag) n] (so [len] is [n], every element the zero
    value) — a freshly-allocated slice, hence no aliasing concern.  Its intended
    Go is [make([]T, n)] (element type from the tag, [n] the length).
    (The 3-arg [make([]T, len, cap)] and [copy] involve the backing-array /
    aliasing model — deferred.) *)
Definition slice_make {A : Type} (tag : GoTypeTag A) (n : nat) : GoSlice A :=
  List.repeat (zero_val tag) n.

(** Indexed access (Go spec "Index expressions") — returns [IO A] because Go panics on out-of-bounds.

    ESCAPE HATCH: the raw panicking form; use inside [catch] to handle OOB.
    Prefer [slice_at_ok] (below), the safe-by-construction default.  TODO: a
    proof-carrying [slice_at xs i (i < len xs)] → [xs[i]] unguarded.

    DEFINITION: [GoSlice A = list A], so the read is the i'th
    element; out of bounds (incl. a negative index) PANICS, like Go.  Its
    intended Go is an [xs[i]] read (the body is suppressed and [Extraction
    NoInline]'d), so this body affects only PROOFS, never the emitted Go — AND it
    must pull in NO external stdlib function (those would enter the extraction
    closure and leak), so the lookup is the SELF-CONTAINED, [int]-indexed
    [go_list_nth] (structural on the list, suppressed) rather than
    [nth_error]+[Z.to_nat].  The signed guard [0 <= i < len xs] decides in-range;
    in range ⇒ the element, else ⇒ panic. *)
Fixpoint go_list_nth {A : Type} (xs : list A) (i : nat) (d : A) : A :=
  match xs with
  | nil        => d
  | x :: rest  => if Nat.eqb i 0 then x
                  else go_list_nth rest (Nat.pred i) d
  end.
Definition slice_get {A : Type} (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) : IO A :=
  fun w => if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool
           then ORet (go_list_nth xs (Z.to_nat (intraw i)) (zero_val tag)) w
           else OPanic (rt_index_oob (intraw i) (List.length xs)) w.
(* ONE length authority: the guard AND the panic payload both consult the STRUCTURAL [List.length]
   (Go's runtime check compares against the true length), never a round-trip through the wrapped
   [len] — so a panic payload tells the truth on ALL model states, sealed two-sided just below.
   On representable slices this is provably the same guard ([len_agrees_structural]). *)
Lemma slice_get_in_bounds : forall {A} (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) w,
  (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool = true ->
  slice_get tag xs i w = ORet (go_list_nth xs (Z.to_nat (intraw i)) (zero_val tag)) w.
Proof. intros A tag xs i w H. unfold slice_get. rewrite H. reflexivity. Qed.
Lemma slice_get_oob_payload : forall {A} (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) w,
  (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool = false ->
  slice_get tag xs i w = OPanic (rt_index_oob (intraw i) (List.length xs)) w.
Proof. intros A tag xs i w H. unfold slice_get. rewrite H. reflexivity. Qed.
(** The [slice_get] bounds surface, manifest-gated (PROGRESS "Current gates"): the two-sided
    guard/payload pin + the wrapped-[len] agreement seal, certified zero-axiom as a bundle. *)
Definition slice_get_bounds_surface :=
  (@slice_get_in_bounds, @slice_get_oob_payload, @len_agrees_structural).
Print Assumptions slice_get_bounds_surface.

(** Safe checked index (the safe-by-construction default for slice access).
    [slice_at_ok tag xs i (fun v ok => body)] bounds-checks [i]: if it is in
    range then [v = xs[i]] and [ok = true]; otherwise [v] is the zero value and
    [ok = false].  CPS like [recv_ok]; because the caller must handle [ok =
    false], this form cannot panic out of bounds.  [i : GoInt] is SIGNED ([Z]-carried),
    so the check covers BOTH ends ([0 <= i < len]); a negative index is in range
    for Go's panic, so it must yield [ok = false], not slip through.

    DEFINITION: bounds-check the SIGNED index, then read via the
    self-contained [go_list_nth] (no stdlib dep, same reason as [slice_get]); in
    range ⇒ [k v true], else ⇒ [k zero false].  Lowered BY NAME (body suppressed
    + NoInline), so it affects only proofs. *)
Definition slice_at_ok {A B : Type}
  (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) (k : A -> bool -> IO B) : IO B :=
  if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool
  then k (go_list_nth xs (Z.to_nat (intraw i)) (zero_val tag)) true
  else k (zero_val tag) false.


(** ---- Arrays (Go spec "Array types"): a FIXED-SIZE [N]T VALUE ----
    Go's [N]T carries the size [N] in the TYPE, but Coq extraction ERASES value-level
    type indices, so [N] is unrecoverable from the extracted type.  The way around it
    for LOCAL arrays: keep the size OUT of the Coq type ([GoArray A], size-erased) and
    put it in the CONSTRUCTION — [arr_lit l] lowers to [[len(l)]T{…}] (the size read off
    the list, exactly as [slice_of_list] reads it for [[]T{…}]).  A local [a := arr_lit …]
    then has its Go type INFERRED from the literal, so no bare
    [[N]T] annotation is emitted.  Distinct from a slice: VALUE semantics, fixed length (an
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
    as [[3]T].  Its constructor [mkArr3] CARRIES A PROOF that its list has length 3,
    so the length is 3 BY CONSTRUCTION — a wrong-length [mkArr3 []] is
    UNCONSTRUCTABLE (the proof obligation [length [] = 3] is unprovable); [arr3_lit] discharges
    it by [eq_refl].  The proof is a [Prop] field, erased at extraction, so [[3]T] is unchanged.
    (Other fixed sizes are their own type; arbitrary type-level [N] is a deferred route.) *)
Record GoArr3 (A : Type) := mkArr3 { arr3_data : list A ; arr3_len : List.length arr3_data = 3%nat }.
Arguments mkArr3 {A} _ _.  Arguments arr3_data {A} _.  Arguments arr3_len {A} _.
Definition arr3_lit {A} (_ : GoTypeTag A) (x y z : A) : GoArr3 A := mkArr3 (x :: y :: z :: nil) eq_refl.
(* Another size — ANY [GoArr<N>] is handled generically (N read from the name). *)
Record GoArr2 (A : Type) := mkArr2 { arr2_data : list A ; arr2_len : List.length arr2_data = 2%nat }.
Arguments mkArr2 {A} _ _.  Arguments arr2_data {A} _.  Arguments arr2_len {A} _.
Definition arr2_lit {A} (_ : GoTypeTag A) (x y : A) : GoArr2 A := mkArr2 (x :: y :: nil) eq_refl.

(** Safe indexed read (CPS / comma-ok like [slice_at_ok] — Go arrays panic on OOB too):
    in range ⇒ [k a[i] true], else [k zero false].  The signed guard covers both ends.
    Lowers IDENTICALLY to [slice_at_ok] (array and slice both index [a[i]] with [len(a)]),
    reusing that arm. *)
Definition arr_get_ok {A B} (tag : GoTypeTag A) (a : GoArray A) (i : GoInt) (k : A -> bool -> IO B) : IO B :=
  if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length (arr_data a))))%bool
  then k (go_list_nth (arr_data a) (Z.to_nat (intraw i)) (zero_val tag)) true
  else k (zero_val tag) false.

(* The construction round-trips: [arr_lit]'s data IS the given list (so [arr_get_ok]
   reads the i'th element placed). *)
Lemma arr_data_lit : forall {A} (tag : GoTypeTag A) (l : list A), arr_data (arr_lit tag l) = l.
Proof. reflexivity. Qed.

(** [slice_at_ok] / [arr_get_ok] STRUCTURAL CORRECTNESS: the comma-ok safe index delivers [(xs[i], true)] when
    [i] is in range ([0 <= i < List.length xs]) and [(zero_val, false)] out of range ([i < 0] OR
    [List.length xs <= i]) — the safe-by-construction read that CANNOT panic (the caller handles [ok = false]).
    The SIGNED bound covers BOTH ends, so a NEGATIVE index yields [ok = false].  Faithful on ALL states, NO
    representability premise: the guard consults the STRUCTURAL [List.length] directly (like [slice_get]), so
    there is no wrapped-[len] disagreement and no executable bad path.  IO-level equations — world-independent. *)
Lemma slice_at_ok_in_range : forall {A B} (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) (k : A -> bool -> IO B),
  (0 <= intraw i < Z.of_nat (List.length xs))%Z ->
  slice_at_ok tag xs i k = k (go_list_nth xs (Z.to_nat (intraw i)) (zero_val tag)) true.
Proof.
  intros A B tag xs i k [Hlo Hhi]. unfold slice_at_ok.
  assert (Hg : (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool = true).
  { apply andb_true_intro. split.
    - apply (proj2 (Z.leb_le 0 (intraw i))). exact Hlo.
    - apply (proj2 (Z.ltb_lt (intraw i) (Z.of_nat (List.length xs)))). exact Hhi. }
  rewrite Hg. reflexivity.
Qed.
Lemma slice_at_ok_oob : forall {A B} (tag : GoTypeTag A) (xs : GoSlice A) (i : GoInt) (k : A -> bool -> IO B),
  (intraw i < 0 \/ Z.of_nat (List.length xs) <= intraw i)%Z ->
  slice_at_ok tag xs i k = k (zero_val tag) false.
Proof.
  intros A B tag xs i k Hout. unfold slice_at_ok.
  destruct (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length xs)))%bool eqn:E.
  - exfalso. apply andb_prop in E. destruct E as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. destruct Hout; lia.
  - reflexivity.
Qed.
Lemma arr_get_ok_in_range : forall {A B} (tag : GoTypeTag A) (a : GoArray A) (i : GoInt) (k : A -> bool -> IO B),
  (0 <= intraw i < Z.of_nat (List.length (arr_data a)))%Z ->
  arr_get_ok tag a i k = k (go_list_nth (arr_data a) (Z.to_nat (intraw i)) (zero_val tag)) true.
Proof.
  intros A B tag a i k [Hlo Hhi]. unfold arr_get_ok.
  assert (Hg : (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length (arr_data a))))%bool = true).
  { apply andb_true_intro. split.
    - apply (proj2 (Z.leb_le 0 (intraw i))). exact Hlo.
    - apply (proj2 (Z.ltb_lt (intraw i) (Z.of_nat (List.length (arr_data a))))). exact Hhi. }
  rewrite Hg. reflexivity.
Qed.
Lemma arr_get_ok_oob : forall {A B} (tag : GoTypeTag A) (a : GoArray A) (i : GoInt) (k : A -> bool -> IO B),
  (intraw i < 0 \/ Z.of_nat (List.length (arr_data a)) <= intraw i)%Z ->
  arr_get_ok tag a i k = k (zero_val tag) false.
Proof.
  intros A B tag a i k Hout. unfold arr_get_ok.
  destruct (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length (arr_data a))))%bool eqn:E.
  - exfalso. apply andb_prop in E. destruct E as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. destruct Hout; lia.
  - reflexivity.
Qed.
(** SLICE/ARRAY SAFE-INDEX SURFACE (manifest-gated, zero-axiom): the comma-ok safe index [slice_at_ok] /
    [arr_get_ok] delivers the element + [true] for a STRUCTURALLY in-range index ([0 <= i < List.length]) and
    the zero value + [false] out of range — the safe-by-construction, panic-free slice/array read.  FAITHFUL on
    ALL states with NO representability premise: like [slice_get] (and [arr_set]), the guard consults the
    STRUCTURAL length directly, so there is no wrapped-[len] disagreement and no executable bad path.  The
    check-and-branch dual of the panicking [slice_get] ([slice_get_bounds_surface]). *)
Definition slice_index_ok_surface :=
  (@slice_at_ok_in_range, @slice_at_ok_oob, @arr_get_ok_in_range, @arr_get_ok_oob).
Print Assumptions slice_index_ok_surface.


(** Array VALUE-COPY (the defining array-vs-slice distinction): [b := arr_set a i v] is
    [a] with element [i] replaced — a FUNCTIONAL update, so [a] is UNCHANGED (value
    semantics; a slice would share the backing).  Lowers to the copy-mutate-return IIFE
    [func(_a [n]T) [n]T { _a[i] = v; return _a }(a)] — Go copies [a] into the value
    parameter, mutates the COPY, and returns it, leaving [a] untouched.  [n] (the size,
    erased from the Coq type) is passed explicitly (the author knows it — the
    size-in-construction principle), so the [n]T] annotation can be emitted.
    EVIDENCE-CARRYING: a Go array assignment [a[i] = v] panics on a
    dynamic out-of-range index, so [arr_set] DEMANDS [0 <= i < len(a)].  The [Prop] witness
    is erased at extraction (native [a[i] = v] does the runtime check). *)
Fixpoint go_list_set {A} (xs : list A) (i : nat) (v : A) : list A :=
  match xs with
  | nil => nil
  | x :: xs' => if Nat.eqb i 0 then v :: xs'
                else x :: go_list_set xs' (Nat.pred i) v
  end.
Definition arr_set {A} (_n : nat) (_ : GoTypeTag A) (a : GoArray A) (i : GoInt) (v : A)
                   (_h : (Z.leb 0 (intraw i) && Z.ltb (intraw i) (Z.of_nat (List.length (arr_data a))))%bool = true) : GoArray A :=
  mkArray (go_list_set (arr_data a) (Z.to_nat (intraw i)) v).


(** ---- Bounded iteration (loops) ----

    [for_each xs body] runs [body] on each element of [xs], in order.  It is a
    total Fixpoint (structural recursion on the slice), so it always terminates
    and its unfolding is a provable equation:
      [for_each nil body = ret tt]
      [for_each (x :: rest) body = body x >>' for_each rest body]
    Its intended Go is a [for _, x := range xs { body }] loop
    rather than recursion, so there is no unbounded stack and the generated
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
    Its intended Go for a [let acc := slice_fold xs init step in …] is an
    accumulator loop:
      [acc := init; for _, x := range xs { acc = step acc x }; …]
    so e.g. summing a slice is a real Go [for] loop, and "the running sum does
    not overflow" is provable on the model (see [i64_add_no_overflow_exact] in main.v). *)
Fixpoint slice_fold {A S : Type} (xs : GoSlice A) (init : S) (step : S -> A -> S) : S :=
  match xs with
  | nil        => init
  | cons x rest => slice_fold rest (step init x) step
  end.

(** ==================================================================================================
    VARIADIC PARAMS + ARRAY COMPARABILITY — [Variadic T]/[vararg] (a variadic param IS a slice;
    the phantom field keeps the param type distinguishable so its intended Go is [...T]), and the
    field-wise array [==] deciders ([arr_eqb]/[arr3_eqb]/[arr2_eqb] over [goi64_list_eqb]).
    Pure.
    ================================================================================================ *)

(** Variadic parameter (Go [func f(xs ...T)]): inside [f] the param is a SLICE, but Go's call
    syntax SPREADS — [f(slice...)].  [Variadic T] is a 2-FIELD record (the [bool] phantom stops
    Coq from unboxing the single slice field, so the PARAM TYPE stays distinguishable from a
    plain [[]T] — its intended Go is [...T], not [[]T]; no [Comparable] is needed for a
    variadic param so the phantom-breaks-equality issue that ruled this out for [GoI64] does
    not apply here).  [vararg xs] marks a call argument for spreading ([xs...]); inside [f],
    [va_slice] recovers the slice (it IS the param itself — the projection is erased, no Go emitted). *)
Record Variadic (T : Type) := MkVariadic { va_slice : GoSlice T ; va_ph : bool }.
Arguments MkVariadic {T} _ _.
Arguments va_slice {T} _.  Arguments va_ph {T} _.
Definition vararg {T} (xs : GoSlice T) : Variadic T := MkVariadic xs true.


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

(** ---- Indexed [range] over a slice (Go spec "For statements: For range"): [for i, x := range xs] ----
    [i] is the element INDEX (0, 1, 2, …), [x] the element — the indexed counterpart of
    [for_each] (which discards the index).  The index is the Go [int] index type (the [Z]-carried [GoInt]).
    Lowers to the native two-variable [for i, x := range xs]; the accumulator model below is
    proof-only (recognized by name, decl suppressed). *)
Fixpoint for_each_idx_from {A : Type} (i : GoInt) (xs : GoSlice A) (body : GoInt -> A -> IO unit) : IO unit :=
  match xs with
  | nil         => ret tt
  | cons x rest => bind (body i x) (fun _ => for_each_idx_from (int_add i (intwrap 1)) rest body)
  end.
Definition for_each_idx {A : Type} (xs : GoSlice A) (body : GoInt -> A -> IO unit) : IO unit :=
  for_each_idx_from (intwrap 0) xs body.
