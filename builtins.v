(** builtins — the OP LAYER of the modelled Go: the IO-typed operations over the split-out
    foundations (the import block below; plans/builtins-split.md).  ★FROZEN
    raw ore (CLAUDE.md): never grows; being mined into final-purpose modules, then deleted. *)

Require Import Coq.Init.Specif.
Require Import Coq.Classes.Morphisms.   (* Proper / setoid rewriting for [io_eq] — replaces funext *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.   (* app / tl for the channel FIFO buffer model *)
From Stdlib Require Import Lia.   (* happens-before timestamp arithmetic *)
From Stdlib Require Import ZArith.   (* Z.to_nat for the slice index *)
From Stdlib Require Import StrictProp.   (* Squash: carry a range invariant in SProp (proof-irrelevant ⇒ wrapper equality decided by the carrier alone, no axiom) *)
From Fido Require Import GoNumeric.   (* the numeric model (split wave 1) — ints + spec_float floats *)
From Fido Require Import GoRuntimeTypes.   (* the runtime type layer (split wave 2) — carriers + GoTypeTag + GoAny + zero_val *)
From Fido Require Import GoEffects.   (* the effect model (split wave 3) — World/Outcome/IO/io_eq/Hoare *)
From Fido Require Import GoPanic.     (* the runtime panic payloads (split wave 4) *)
From Fido Require Import GoSlice.     (* the pure-list slice/array model (split wave 5) *)
From Fido Require Import GoMap.       (* Go maps over the world heap (split wave 6) *)
From Fido Require Import GoChan.      (* Go channels + the go-mem story (split wave 7) *)
From Fido Require Import GoHeap.      (* the ref heap — locals/pointers/SliceH/struct heap (split wave 8) *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
(* No [PrimInt63] / [PrimFloat] imports: the numeric model is AXIOM-FREE — integers are [Z]-carried
   records, heap locations [nat], floats [SpecFloat.spec_float]. *)




(** Function VALUES.  [gofunc_of] wraps a real closure as a non-nil [GoFunc]; the
    [zero_val (TArrow ..) = None] nil func is the ONLY other inhabitant.  [gofunc_call] is the
    EFFECTFUL invocation: a real closure runs, but a [nil] ([None]) func PANICS with Go's exact
    nil-dereference message ([rt_nil_deref]).  So a nil func is never a silently-callable
    placeholder — extraction emits the bare Go call [f(x)], whose runtime nil-panic MATCHES. *)
Definition gofunc_of {A B} (f : A -> B) : GoFunc A B := SomeFunc f.
Definition gofunc_call {A B} (f : GoFunc A B) (x : A) : IO B :=
  match f with
  | SomeFunc g => ret (g x)
  | NilFunc    => panic rt_nil_deref
  end.
Lemma gofunc_call_of : forall {A B} (f : A -> B) (x : A) (w : World),
  run_io (gofunc_call (gofunc_of f) x) w = ORet (f x) w.
Proof. reflexivity. Qed.
Lemma gofunc_call_nil : forall {A B} (x : A) (w : World),
  run_io (gofunc_call (@NilFunc A B) x) w = OPanic rt_nil_deref w.
Proof. reflexivity. Qed.

(** ---- Builtins ---- *)

(** [print]/[println] write to stdout — a RECORDED effect: each call appends an event
    [(is_println, args)] to the world's [w_output] trace, so programs that print different
    things are not [run_io]-equal.  Lowered BY NAME to native Go [print]/[println]; the
    trace is proof-only and never extracted. *)
Definition w_log (b : bool) (xs : list GoAny) (w : World) : World :=
  mkWorld (w_refs w) (w_chans w) (w_maps w) (w_next w) (w_output w ++ ((b, xs) :: nil)).
Definition print   (xs : list GoAny) : IO unit := fun w => ORet tt (w_log false xs w).
Definition println (xs : list GoAny) : IO unit := fun w => ORet tt (w_log true xs w).

(** [run_io] RESPECTS output — a program that prints TWICE is not provably equal to
    one that prints ONCE.  The result worlds differ in their [w_output] trace length. *)
Example output_distinguishes_programs :
  run_io (bind (println nil) (fun _ => println nil)) w_init
  <> run_io (println nil) w_init.
Proof. vm_compute. discriminate. Qed.

(** [panic], [bind_panic_l], and the PANIC-SENSITIVE Hoare logic ([hoare_panic_unreachable] /
    [hoare_no_panic]) are defined up top with the panic-aware semantics; all are proved lemmas. *)

(** ---- panic / recover semantics ----

    [catch m h] is the semantic of [defer func() { if r := recover(); r != nil { h(r) } }()].
    [recover()] in Go is just the panic value bound by [h] — it needs no separate axiom.

    Compound panics: if [h] itself panics with [w], [catch (panic v) h = h v = panic w],
    so the new panic [w] replaces [v].  This is correct Go semantics and falls out from
    [catch_panic] alone — no extra law needed.

    [with_defer] models [defer cleanup()] (without recover): runs [cleanup] on both
    normal exit and panic exit.  If [cleanup] panics mid-panic, the new panic wins —
    also correct Go semantics, again from [catch_panic] + [bind_panic_l]. *)

(** [catch] is declared up top; [catch_ret] and [catch_panic] are proved
    lemmas (from [run_catch]), not axioms. *)

(** [with_defer cleanup m]: run [m], then run [cleanup] EXACTLY ONCE regardless
    of outcome (Go runs one deferred call once).  If [cleanup] panics, its panic
    replaces any in-flight panic.
    Invariant: cleanup does NOT live inside the [catch] that distinguishes the
    body outcome — [m]'s outcome is reified into a [GoAny + A] sum WITHOUT running
    cleanup, then cleanup runs exactly once on the single post-[catch] path and
    the captured body panic is re-raised. *)
Definition with_defer {A : Type} (cleanup : IO unit) (m : IO A) : IO A :=
  r <-' catch (x <-' m ;; ret (@inr GoAny A x)) (fun v => ret (@inl GoAny A v)) ;;
  cleanup >>' match r with
              | inl v => panic v
              | inr x => ret x
              end.

(** When the guarded body panics, the deferred [cleanup] still runs and the
    original panic propagates afterwards.  Follows from [bind_panic_l] (panic
    short-circuits the body, reifying nothing) and [catch_panic] (the handler
    captures the panic as [inl v]); cleanup then runs once and re-raises it. *)
Lemma with_defer_panic : forall {A} (cleanup : IO unit) (v : GoAny),
  @with_defer A cleanup (panic v) =io= cleanup >>' panic v.
Proof.
  intros A cleanup v. unfold with_defer.
  rewrite bind_panic_l, catch_panic, bind_ret_l. reflexivity.
Qed.

(** Companion lemma for the NORMAL path: when the body returns [x], cleanup runs
    and [x] propagates.  Crucially this holds UNCONDITIONALLY in [cleanup] — even
    a [cleanup] that panics is run exactly once (the RHS mentions [cleanup] once);
    together with [with_defer_panic] it certifies a single cleanup execution on
    both exits. *)
Lemma with_defer_ret : forall {A} (cleanup : IO unit) (x : A),
  @with_defer A cleanup (ret x) =io= cleanup >>' ret x.
Proof.
  intros A cleanup x. unfold with_defer.
  rewrite bind_ret_l, catch_ret, bind_ret_l. reflexivity.
Qed.

(** [defer_call f] (Go spec "Defer statements"): Go's [defer] keyword — schedule [f] to run when the
    enclosing *function* returns (LIFO across all defers, on both normal and panic exit).  FUNCTION-scoped,
    unlike block-scoped [with_defer].  Lowers to [defer func(){ f }()] (Go provides the function-scoping,
    LIFO ordering, run-at-return).

    FAILS LOUD in the sequential [run_io] semantics: shallow [World -> Outcome] cannot run a
    func-scoped defer (it cannot reify the deferred command to run it at return), so the sequential
    meaning is a LOUD panic rather than a silent drop of an observable effect.  The FAITHFUL defer
    is [run_cmd] over a [CDfr] node (cmd.v), which runs defers LIFO at func-scope return, on panic
    too.  Extraction is unaffected: the plugin lowers [defer_call] BY NAME to a real
    [defer func(){…}()] (this body is suppressed). *)
Definition defer_call (_ : IO unit) : IO unit :=
  fun w => OPanic (anyt TString "fido: defer_call has no shallow run_io meaning — a func-scoped defer needs the deep command model; the faithful semantics is run_cmd's CDfr (cmd.v); run_io fails loud rather than silently dropping the deferred effect"%string) w.


(** [type_assert tag v] (Go spec "Type assertions") asserts that [v : GoAny] holds
    a value of Go type [T].  Panics (like Go's [v.(T)]) if the runtime type does not
    match.

    ESCAPE HATCH: the raw panicking form, safe only inside [catch] or when the
    runtime type is already known.  Prefer [type_assert_safe] (below), the
    safe-by-construction default.

    The tagged [GoAny] carries the value's runtime [GoTypeTag], so [tag_coerce]
    checks it against the target [tag] and recovers the value when they agree; a
    mismatch PANICS, exactly Go's [v.(T)].  Lowered by NAME to [v.(T)] (body
    suppressed). *)
Definition type_assert {T : Type} (tag : GoTypeTag T) (a : GoAny) : IO T :=
  match a with
  | existT _ _ (x, atag) =>
      match tag_coerce tag atag x with
      | Some t => ret t
      | None   => panic rt_assert_fail   (* runtime-type mismatch: Go panics *)
      end
  end.

(** Read-after-assert: asserting [anyt tag x] to its OWN tag returns [x] — a THEOREM,
    from [tag_coerce_refl]. *)
Theorem type_assert_ok : forall {T} (tag : GoTypeTag T) (x : T),
  type_assert tag (anyt tag x) = ret x.
Proof. intros T tag x. unfold type_assert. rewrite tag_coerce_refl. reflexivity. Qed.

(** Safe checked assertion (the safe-by-construction default for [GoAny]).
    [type_assert_safe tag a (fun v ok => body)] lowers to Go's native
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
Example type_assert_safe_ok : forall {B} (x : GoInt) (k : GoInt -> bool -> IO B),
  type_assert_safe TInt64 (anyt TInt64 x) k = k x true.
Proof. intros B x k. unfold type_assert_safe. rewrite tag_coerce_refl. reflexivity. Qed.
Example type_assert_safe_mismatch : forall {B} (x : GoInt) (k : bool -> bool -> IO B),
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
Example type_switch2_default : forall {B} (x : GoInt) k1 k2 (d : IO B),
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
Example type_switch_or2_default : forall {B} (x : GoInt) (k d : IO B),
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
Example type_switch_or3_default : forall {B} (x : GoInt) (k d : IO B),
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

(** [min]/[max] (Go 1.21 predeclared builtins) on [int] — the smaller / larger of
    two values, by the SIGNED ordering (Go's int [<]), so [go_min] = Go [min(a,b)]
    and [go_max] = Go [max(a,b)] for the [int] type.  Computable (so [go_min 3 5 =
    3] is a THEOREM); the plugin lowers the call to Go's builtin.  (Go's [min]/[max]
    also apply to floats — with NaN/`-0` corner cases — and strings; those follow
    once those orderings are settled.) *)
Definition go_min (a b : GoInt) : GoInt := if int_ltb a b then a else b.
Definition go_max (a b : GoInt) : GoInt := if int_ltb a b then b else a.

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
Definition f64_min (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then a
  else if SFltb b a then b
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then a else b)   (* min wants -0 *)
    else a.
Definition f64_max (a b : GoFloat64) : GoFloat64 :=
  if negb (SFeqb a a) then a            (* a is NaN → NaN *)
  else if negb (SFeqb b b) then b       (* b is NaN → NaN *)
  else if SFltb a b then b
  else if SFltb b a then a
  else (* numerically equal (incl. ±0) *)
    if SFeqb a (S754_zero false)
    then (if SFltb (SFdiv 53 1024 (sf_of_Z 1) a) (S754_zero false) then b else a)   (* max wants +0 *)
    else a.

(** Direct [>] / [>=] / [!=] for float64.  CRUCIAL NaN subtlety: [>=] is NOT
    [¬(<)] — with a NaN operand, [a >= b] is FALSE (Go/IEEE), whereas [¬(a < b)]
    would be TRUE.  So [f64_geb] is the SWAPPED [leb] ([b <= a]), and [f64_gtb] the
    swapped [ltb] — both correctly false on NaN.  [f64_neqb] IS [negb (eqb)] (a NaN
    compares UNEQUAL to everything, so [a != b] is true — matching [negb false]). *)
Definition f64_gtb  (a b : GoFloat64) : bool := SFltb b a.
Definition f64_geb  (a b : GoFloat64) : bool := SFleb b a.
Definition f64_neqb (a b : GoFloat64) : bool := negb (SFeqb a b).


(** Variadic parameter (Go [func f(xs ...T)]): inside [f] the param is a SLICE, but Go's call
    syntax SPREADS — [f(slice...)].  [Variadic T] is a 2-FIELD record (the [bool] phantom stops
    Coq from unboxing the single slice field, so the PARAM TYPE stays distinguishable from a
    plain [[]T] — the plugin renders it [...T], not [[]T]; no [Comparable] is needed for a
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

(** ---- String operations (Go spec "String types") ----

    [str_len s] is the BYTE length (Go [len(s)]): a computable [int] that counts
    the [string]'s bytes, so [str_len "Go" = 2] is a THEOREM.  The plugin lowers
    it to Go [int64(len(s))] — the byte count in the [Z]-carried [GoInt] (int64) model.

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
Fixpoint str_len (s : GoString) : GoInt :=
  match s with
  | EmptyString   => intwrap 0
  | String _ rest => intwrap (1 + intraw (str_len rest))
  end.

(** DEFINITION: the i'th BYTE of the string at the signed index,
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
      let v (b : bool) (k : Z) : Z := if b then k else 0%Z in
      u8wrap (v b0 1 + (v b1 2 + (v b2 4 + (v b3 8 +
             (v b4 16 + (v b5 32 + (v b6 64 + v b7 128)))))))%Z
  end.
Fixpoint go_str_byte (s : GoString) (i : nat) : GoByte :=
  match s with
  | EmptyString  => u8wrap 0
  | String c rest => if Nat.eqb i 0 then ascii_byte c
                     else go_str_byte rest (Nat.pred i)
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
  let bit (k : Z) : bool := Z.testbit n k in
  Ascii (bit 0%Z) (bit 1%Z) (bit 2%Z) (bit 3%Z)
        (bit 4%Z) (bit 5%Z) (bit 6%Z) (bit 7%Z).
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
  (s : GoString) (i : GoInt) (k : GoByte -> bool -> IO B) : IO B :=
  if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (intraw (str_len s)))%bool
  then k (go_str_byte s (Z.to_nat (intraw i))) true
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
    [nat] (a string length/offset is non-negative).  The body [String.substring a (b-a) s] is recognized
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
Definition byte_chr (v : Z) : ascii := byte_ascii (u8wrap v).

(** [str_to_runes] is a FAITHFUL UTF-8 decoder — exactly Go's [utf8.DecodeRune] /
    range-over-string.  An invalid sequence yields [RuneError] (U+FFFD) and advances by exactly ONE byte
    (NOT the would-be width), rejecting: continuation bytes used as leads (0x80–0xBF), overlong 2-byte
    (0xC0/0xC1), missing/bad continuation bytes, overlong 3/4-byte (0xE0 with c1<0xA0; 0xF0 with c1<0x90),
    UTF-16 surrogates (0xED with c1≥0xA0), >MaxRune (0xF4 with c1≥0x90), and invalid leads ≥0xF5.  The body
    is proof-only (lowered by name to native [[]rune(s)], which does the same). *)
(** [str_to_runes_w] decodes AND records, per rune, the number of SOURCE bytes consumed (1 for an
    invalid byte — Go's [utf8.DecodeRune] advances exactly one — or the 2/3/4 of a valid multibyte).
    That CONSUMED width, not the decoded rune's would-be re-encoded width, is what [str_range]
    accumulates into byte offsets: for source [0x80 'A'] Go yields
    [(0,U+FFFD) (1,'A')], and so does the model (the FFFD consumed ONE byte, not
    [rune_width U+FFFD] = 3).  [str_to_runes] (rune-only) is [map fst] of this — one decoder. *)
Fixpoint str_to_runes_w (s : GoString) : list (GoI32 * Z) :=
  match s with
  | EmptyString => nil
  | String c0 r0 =>
      (* [rerr]/[isc] are LOCAL (not top-level Definitions): the whole body is suppressed and lowered by
         name to native [[]rune(s)], so the unsigned [ltb]/[leb] here are proof-only and never extracted. *)
      let rerr := i32wrap 65533%Z in              (* U+FFFD *)
      let isc  := fun v => andb (Z.leb 128%Z v) (Z.ltb v 192%Z) in  (* cont byte 0x80–0xBF *)
      let v0 := u8raw (ascii_byte c0) in
      if Z.ltb v0 128%Z then              (* 1-byte: ASCII 0x00–0x7F *)
        (i32wrap v0, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 194%Z then         (* 0x80–0xC1: cont-as-lead OR overlong-2 → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 224%Z then         (* 0xC2–0xDF: 2-byte (result ≥ 0x80, non-overlong) *)
        match r0 with
        | String c1 r1 =>
            let v1 := u8raw (ascii_byte c1) in
            if isc v1 then
              (i32wrap (Z.lor (Z.shiftl (Z.land v0 31%Z) 6%Z)
                                     (Z.land v1 63%Z)), 2%Z) :: str_to_runes_w r1
            else (rerr, 1%Z) :: str_to_runes_w r0   (* bad continuation → error, advance 1 *)
        | EmptyString => (rerr, 1%Z) :: nil         (* truncated → advance 1 (the lead) *)
        end
      else if Z.ltb v0 240%Z then         (* 0xE0–0xEF: 3-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xE0→[0xA0,0xBF] (overlong); 0xED→[0x80,0x9F] (surrogate) *)
              if Z.eqb v0 224%Z then andb (Z.leb 160%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 237%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 160%Z)
              else isc v1 in
            match r1' with
            | String c2 r2 =>
                let v2 := u8raw (ascii_byte c2) in
                if andb v1ok (isc v2) then
                  (i32wrap (Z.lor (Z.lor
                           (Z.shiftl (Z.land v0 15%Z) 12%Z)
                           (Z.shiftl (Z.land v1 63%Z) 6%Z))
                           (Z.land v2 63%Z)), 3%Z) :: str_to_runes_w r2
                else (rerr, 1%Z) :: str_to_runes_w r0
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else if Z.ltb v0 245%Z then         (* 0xF0–0xF4: 4-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xF0→[0x90,0xBF] (overlong); 0xF4→[0x80,0x8F] (>MaxRune) *)
              if Z.eqb v0 240%Z then andb (Z.leb 144%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 244%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 144%Z)
              else isc v1 in
            match r1' with
            | String c2 r2' =>
                let v2 := u8raw (ascii_byte c2) in
                match r2' with
                | String c3 r3 =>
                    let v3 := u8raw (ascii_byte c3) in
                    if andb v1ok (andb (isc v2) (isc v3)) then
                      (i32wrap (Z.lor (Z.lor (Z.lor
                               (Z.shiftl (Z.land v0 7%Z) 18%Z)
                               (Z.shiftl (Z.land v1 63%Z) 12%Z))
                               (Z.shiftl (Z.land v2 63%Z) 6%Z))
                               (Z.land v3 63%Z)), 4%Z) :: str_to_runes_w r3
                    else (rerr, 1%Z) :: str_to_runes_w r0
                | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
                end
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else                                             (* 0xF5–0xFF: invalid lead → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
  end.
(* rune-only view = drop the consumed-width tags.  A manual fixpoint (not [List.map]) so the
   suppressed body pulls no generic [map] into the extraction closure. *)
Fixpoint str_runes_fst (rs : list (GoI32 * Z)) : list GoI32 :=
  match rs with
  | nil              => nil
  | cons (r, _) rest => cons r (str_runes_fst rest)
  end.
Definition str_to_runes (s : GoString) : list GoI32 := str_runes_fst (str_to_runes_w s).
Definition rune_bytes (r : GoI32) : GoString :=
  (* Go's [string(rune)] / [utf8.EncodeRune] replaces an out-of-range or surrogate rune with
     U+FFFD: Go tests [uint32(r) > MaxRune], so a NEGATIVE int32 is out of range —
     on our [Z] carrier that is simply [c0 < 0] (we guard [0 <= c0] below) — as is [r] in the
     UTF-16 surrogate range [0xD800,0xDFFF]. *)
  let c0 := i32raw r in
  (* out-of-range (incl. NEGATIVE — on the [Z] carrier that is [c0 < 0]) or UTF-16
     surrogate → U+FFFD. *)
  let c := if andb (andb (Z.leb 0 c0) (Z.leb c0 1114111))
                   (negb (andb (Z.leb 55296 c0) (Z.leb c0 57343)))
           then c0 else 65533%Z in
  if Z.ltb c 128 then
    String (byte_chr c) EmptyString
  else if Z.ltb c 2048 then
    String (byte_chr (Z.lor 192 (Z.shiftr c 6)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString)
  else if Z.ltb c 65536 then
    String (byte_chr (Z.lor 224 (Z.shiftr c 12)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))
  else
    String (byte_chr (Z.lor 240 (Z.shiftr c 18)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 12) 63)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))).
Fixpoint runes_to_str (rs : list GoI32) : GoString :=
  match rs with
  | nil => EmptyString
  | r :: rest => str_concat (rune_bytes r) (runes_to_str rest)
  end.

(** Codec verified by ROUND-TRIP: encode→decode is the identity for ASCII and for a 3-byte
    CJK code point (中 = U+4E2D = 20013, UTF-8 E4 B8 AD). *)
Example rune_roundtrip_ascii :
  str_to_runes (runes_to_str (i32wrap 65 :: i32wrap 66 :: nil))
    = i32wrap 65 :: i32wrap 66 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example rune_roundtrip_cjk :
  str_to_runes (runes_to_str (i32wrap 20013 :: nil)) = i32wrap 20013 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Witnesses (machine-checked): INVALID UTF-8 decodes to U+FFFD (65533) per offending
    byte, advancing ONE byte — exactly Go's [utf8.DecodeRune].  [byte_chr v] is the byte
    with value [v]. *)
Example utf8_cont_as_lead :                  (* lone continuation 0x80 — not a valid lead → one U+FFFD *)
  str_to_runes (String (byte_chr 128) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_overlong_2 :                     (* 0xC0 0x80 (overlong NUL): 0xC0 bad lead, 0x80 cont → two U+FFFD *)
  str_to_runes (String (byte_chr 192) (String (byte_chr 128) EmptyString))
    = i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_surrogate :                      (* 0xED 0xA0 0x80 (would be U+D800, a UTF-16 surrogate) → three U+FFFD *)
  str_to_runes (String (byte_chr 237) (String (byte_chr 160) (String (byte_chr 128) EmptyString)))
    = i32wrap 65533 :: i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_truncated_2 :                     (* 0xC2 with no continuation → one U+FFFD *)
  str_to_runes (String (byte_chr 194) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_valid_2byte :                     (* 0xC2 0xA9 = U+00A9 (©) still decodes correctly *)
  str_to_runes (String (byte_chr 194) (String (byte_chr 169) EmptyString)) = i32wrap 169 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Single rune → string (Go's [string(rune)]): the 1-code-point UTF-8 string.  Reuses the
    [rune_bytes] encoder; lowers to the native [string(rune(r))] (the explicit [rune] cast
    keeps it out of the deprecated [string(int)] form). *)
Definition rune_to_str (r : GoI32) : GoString := rune_bytes r.
Example rune_to_str_ascii : rune_to_str (i32wrap 65) = "A"%string.
Proof. vm_compute. reflexivity. Qed.
(** An out-of-range or surrogate rune encodes to U+FFFD,
    exactly Go's [string(rune)].  Witnessed against the explicit FFFD encoding [EF BF BD]: a
    UTF-16 surrogate (0xD800), a code point past MaxRune (0x110000), and a NEGATIVE rune (-1,
    built by [i32_sub] so it is a genuine negative int32) all collapse to U+FFFD. *)
Example rune_to_str_surrogate : rune_to_str (i32wrap 55296) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_above_max : rune_to_str (i32wrap 1114112) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_negative :
  rune_to_str (i32_sub (i32wrap 0) (i32wrap 1)) = rune_to_str (i32wrap 65533).
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

(** SEALED: [ComparableW] CARRIES the decidability proof
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
      if Z.ltb na nb then true
      else if Z.ltb nb na then false
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
Record GoComplex128 : Type := MkComplex128 { c_re : GoFloat64 ; c_im : GoFloat64 }.
Definition go_complex (re im : GoFloat64) : GoComplex128 := MkComplex128 re im.
Definition go_real (c : GoComplex128) : GoFloat64 := c_re c.
Definition go_imag (c : GoComplex128) : GoFloat64 := c_im c.

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
  MkComplex128 (f64_add (c_re a) (c_re b)) (f64_add (c_im a) (c_im b)).
Definition complex_sub (a b : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_sub (c_re a) (c_re b)) (f64_sub (c_im a) (c_im b)).

(** Build-checked: each component of the sum/difference is the float add/sub of the
    corresponding components (so the native [a + b] computes exactly what Go does). *)
Example complex_add_components : forall a b,
  go_real (complex_add a b) = f64_add (go_real a) (go_real b)
  /\ go_imag (complex_add a b) = f64_add (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.
Example complex_sub_components : forall a b,
  go_real (complex_sub a b) = f64_sub (go_real a) (go_real b)
  /\ go_imag (complex_sub a b) = f64_sub (go_imag a) (go_imag b).
Proof. intros. split; reflexivity. Qed.

(** Complex COMPARISON — Go's [==] / [!=] on complex128.  Two complex values are equal iff
    BOTH components are equal (Go spec "Comparison operators"); float [==] is EXACT, so this
    is faithful including the NaN corner ([NaN != NaN] ⇒ a complex with a NaN component is
    never [==] itself).  Lowers to the native Go [==] / [!=]. *)
Definition complex_eqb (a b : GoComplex128) : bool :=
  andb (f64_eqb (c_re a) (c_re b)) (f64_eqb (c_im a) (c_im b)).
Definition complex_neqb (a b : GoComplex128) : bool := negb (complex_eqb a b).

(** Build-checked: equality is the component-wise float-[==] conjunction (so the native
    [a == b] decides exactly what Go's complex [==] does). *)
Example complex_eqb_components : forall a b,
  complex_eqb a b = andb (f64_eqb (go_real a) (go_real b)) (f64_eqb (go_imag a) (go_imag b)).
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
    (f64_sub (f64_mul (c_re a) (c_re b)) (f64_mul (c_im a) (c_im b)))
    (f64_add (f64_mul (c_re a) (c_im b)) (f64_mul (c_im a) (c_re b))).

(** Build-checked: the real/imag parts are exactly gc's naive cross products. *)
Example complex_mul_components : forall a b,
  go_real (complex_mul a b)
    = f64_sub (f64_mul (go_real a) (go_real b)) (f64_mul (go_imag a) (go_imag b))
  /\ go_imag (complex_mul a b)
    = f64_add (f64_mul (go_real a) (go_imag b)) (f64_mul (go_imag a) (go_real b)).
Proof. intros. split; reflexivity. Qed.

(** Complex unary NEGATION — Go's [-c] on complex128.  Negates BOTH components, each a
    single IEEE float sign-flip [f64_opp], so faithful including signed zero — note
    [-c] (sign-flip) differs from [(0+0i) - c] on a zero component ([opp (+0) = -0] but
    [0 - (+0) = +0]); we use the sign-flip, matching Go's unary [-].  Lowers to native [-c]. *)
Definition complex_neg (c : GoComplex128) : GoComplex128 :=
  MkComplex128 (f64_opp (c_re c)) (f64_opp (c_im c)).

Example complex_neg_components : forall c,
  go_real (complex_neg c) = f64_opp (go_real c)
  /\ go_imag (complex_neg c) = f64_opp (go_imag c).
Proof. intros. split; reflexivity. Qed.

(** Complex DIVIDE — Go's [/] on complex128.  Unlike [*] (a naive inline), gc lowers [/]
    to [runtime.complex128div], which uses SMITH'S scaling algorithm (divide through by the
    larger-magnitude denominator component, for numerical stability).  This model is exactly
    that algorithm — operand-for-operand the gc source — and it lowers to the native Go [/].
    (The Annex-G-style Inf/NaN recovery postamble for DEGENERATE divisors is modelled too —
    see the branch comment below.) *)
Definition complex_div (n m : GoComplex128) : GoComplex128 :=
  let nr := c_re n in let ni := c_im n in
  let mr := c_re m in let mi := c_im m in
  (* branch on which denominator component is larger in magnitude — Go uses [|mr| >= |mi|], i.e.
     [|mi| <= |mr|].  We compare ABSOLUTE VALUES via [f64_abs] (= [SpecFloat.SFabs], axiom-free):
     abs never overflows, so the branch matches Go even for huge components (a squared-magnitude
     compare would collapse to [Inf <= Inf] and pick the wrong branch).  Sound even though
     [math.Abs] would need an import: [complex_div] lowers to the NATIVE Go [/] (body PROOF-ONLY,
     suppressed by name), so the [abs] is never extracted.
    The DEGENERATE-divisor postamble (C99 Annex G.5.1 step 3 — zero / Inf / NaN denominators) is
    PORTED operand-for-operand from gc's [runtime.complex128div], so the model matches Go on ALL
    inputs, not just finite ones.  NaN/Inf are detected with [spec_float] primitives ([eqb x x] /
    [|x| = +Inf]); [copysign_inf]/[inf2one] reproduce gc's [math.Copysign] (sign of a zero via
    [1.0 / c = -Inf]).  All proof-only — [complex_div] still lowers to native Go [/], whose
    runtime applies exactly this recovery. *)
  let isnan := fun x => negb (f64_eqb x x) in
  let isinf := fun x => f64_eqb (f64_abs x) (S754_infinity false) in
  let isfin := fun x => negb (orb (isnan x) (isinf x)) in
  (* sign bit set (x < 0, or x = -0 detected via 1.0/-0 = -Inf) *)
  let negs  := fun x => orb (f64_ltb x (0%go64))
                            (f64_eqb (f64_div (1%go64) x) (S754_infinity true)) in
  let copysign_inf := fun c => if negs c then (S754_infinity true) else (S754_infinity false) in (* Copysign(+Inf, c) *)
  let inf2one := fun x => let g := if isinf x then (1%go64) else (0%go64) in
                          if negs x then f64_opp g else g in       (* Copysign(isInf?1:0, x) *)
  let res :=
    if f64_leb (f64_abs mi) (f64_abs mr) then
      let ratio := f64_div mi mr in
      let denom := f64_add mr (f64_mul ratio mi) in
      MkComplex128 (f64_div (f64_add nr (f64_mul ni ratio)) denom)
                   (f64_div (f64_sub ni (f64_mul nr ratio)) denom)
    else
      let ratio := f64_div mr mi in
      let denom := f64_add mi (f64_mul ratio mr) in
      MkComplex128 (f64_div (f64_add (f64_mul nr ratio) ni) denom)
                   (f64_div (f64_sub (f64_mul ni ratio) nr) denom) in
  (* Annex-G recovery: only when BOTH components came out NaN (a degenerate divisor) *)
  if andb (isnan (c_re res)) (isnan (c_im res)) then
    let a := nr in let b := ni in let c := mr in let d := mi in
    if andb (andb (f64_eqb c (0%go64)) (f64_eqb d (0%go64)))
            (orb (negb (isnan a)) (negb (isnan b)))                          (* m == 0, n not all-NaN *)
    then MkComplex128 (f64_mul (copysign_inf c) a) (f64_mul (copysign_inf c) b)
    else if andb (orb (isinf a) (isinf b)) (andb (isfin c) (isfin d))        (* Inf numerator / finite denom *)
    then let a' := inf2one a in let b' := inf2one b in
         MkComplex128 (f64_mul (S754_infinity false) (f64_add (f64_mul a' c) (f64_mul b' d)))
                      (f64_mul (S754_infinity false) (f64_sub (f64_mul b' c) (f64_mul a' d)))
    else if andb (orb (isinf c) (isinf d)) (andb (isfin a) (isfin b))        (* finite numerator / Inf denom *)
    then let c' := inf2one c in let d' := inf2one d in
         MkComplex128 (f64_mul (0%go64) (f64_add (f64_mul a c') (f64_mul b d')))
                      (f64_mul (0%go64) (f64_sub (f64_mul b c') (f64_mul a d')))
    else res
  else res.

(** Witness (machine-checked): on a large divisor where BOTH components square to [+Inf]
    (|mi|, |mr| ≳ 1e154) but |mi| > |mr|, a squared-magnitude branch [mi² <= mr²] wrongly reduces
    to [Inf <= Inf = true] (picks the |mr|-branch), while [|mi| <= |mr|] correctly yields [false]
    (the |mi|-branch) — exactly Go's [|mr| >= |mi|].  ([0x1p550] = 2^550, [0x1p600] = 2^600.) *)
Example complex_div_branch_overflow_fixed :
  let mr := binary_normalize 53 1024 1 550 false in let mi := binary_normalize 53 1024 1 600 false in  (* 2^550, 2^600 *)
     f64_leb (f64_mul mi mi) (f64_mul mr mr) = true    (* squared: WRONG branch *)
  /\ f64_leb (f64_abs mi)    (f64_abs mr)    = false.  (* abs:     RIGHT branch *)
Proof. vm_compute. split; reflexivity. Qed.
(** DEGENERATE divisors recover per Annex G (not the bare-Smith NaN).  Finite
    nonzero / ZERO yields infinities; finite / Inf yields zero — matching gc's runtime.complex128div. *)
Example complex_div_by_zero_is_inf :   (* (1+2i)/(0+0i) = (+Inf, +Inf) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (2%go64)) (go_complex (0%go64) (0%go64)))) (S754_infinity false) = true.
Proof. vm_compute. split; reflexivity. Qed.
Example complex_div_by_inf_is_zero :   (* (1+1i)/(Inf+Inf i) = (0, 0) *)
  f64_eqb (c_re (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true
  /\ f64_eqb (c_im (complex_div (go_complex (1%go64) (1%go64)) (go_complex (S754_infinity false) (S754_infinity false)))) (0%go64) = true.
Proof. vm_compute. split; reflexivity. Qed.

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
    by (rewrite chan_buf_send, Hempty; reflexivity).
  rewrite (run_recv (TProd TI64 TI64) (MkChan (ch_loc ch)) v nil _ Hbuf1).
  eexists; reflexivity.
Qed.

(** ---- [range] over a string (Go spec "For statements: For range"): [for i, r := range s] ----
    Go ranges a STRING by UTF-8 code point: [i] is the BYTE offset of each code point's first
    byte, [r] the decoded rune.  Modeled faithfully on the rune view: [str_to_runes_w] decodes
    each rune WITH the number of source bytes it consumed, and the byte offsets are the running
    prefix sums of those CONSUMED widths — exactly Go's string-range index, even for invalid
    UTF-8 (machine-checked by [str_range_offsets] / [str_range_invalid_offsets] in main.v).
    ([rune_width] — utf8.RuneLen, a rune's ENCODED length — is a separate utility.)  [str_range] lowers
    to the NATIVE two-variable [for i, r := range s]; the [for_each_pairs]/[runes_with_offsets]
    model is proof-only (recognized by name, decl suppressed), so the emitted Go is the
    idiomatic range loop — never a [[]rune] materialisation.  The index is the Go [int]
    index type. *)
Definition rune_width (r : GoI32) : Z :=
  let c := i32raw r in
  if Z.ltb c 128   then 1    (* 1-byte (ASCII) *)
  else if Z.ltb c 2048  then 2    (* 2-byte *)
  else if Z.ltb c 65536 then 3    (* 3-byte *)
  else 4.                          (* 4-byte *)
(** Byte offsets are the running prefix sums of the CONSUMED SOURCE widths (the [int] tag from
    [str_to_runes_w]), so an invalid byte advances the offset by ONE — matching Go's range even
    for invalid UTF-8.  Re-encoding the decoded rune (via [rune_width]) would
    OVER-count: U+FFFD is 3 bytes encoded but a malformed byte consumes only 1. *)
Fixpoint runes_with_offsets (off : GoInt) (rs : list (GoI32 * Z)) : list (GoInt * GoI32) :=
  match rs with
  | nil              => nil
  | cons (r, w) rest => cons (off, r) (runes_with_offsets (int_add off (intwrap w)) rest)
  end.
Fixpoint for_each_pairs {A B : Type} (xs : list (A * B)) (body : A -> B -> IO unit) : IO unit :=
  match xs with
  | nil              => ret tt
  | cons (a, b) rest => bind (body a b) (fun _ => for_each_pairs rest body)
  end.
Definition str_range (s : GoString) (body : GoInt -> GoI32 -> IO unit) : IO unit :=
  for_each_pairs (runes_with_offsets (intwrap 0) (str_to_runes_w s)) body.

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

(** ---- Integer [range] (Go 1.22, spec "For statements: For range" over an integer): [for i := range n] ----
    Produces [i = 0, 1, …, n-1] (and runs zero times when [n = 0], exactly Go's rule).
    The bound [n] is the iteration COUNT (a [nat] — non-negative, and the structurally
    DECREASING argument, so termination is by construction with no carrier conversion); the produced index
    [i] is the Go [int] index type (the [Z]-carried [GoInt]).  Recognized by name + decl suppressed, so the
    lowering is the native [for i := range n] (the [nat] count renders as the bound). *)
Fixpoint int_range_aux (i : GoInt) (n : nat) (body : GoInt -> IO unit) : IO unit :=
  match n with
  | O    => ret tt
  | S f  => bind (body i) (fun _ => int_range_aux (int_add i (intwrap 1)) f body)
  end.
Definition int_range (n : nat) (body : GoInt -> IO unit) : IO unit :=
  int_range_aux (intwrap 0) n body.
