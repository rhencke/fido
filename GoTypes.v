(** ============================================================================
    GoTypes.v — the SHARED constant-aware type-category checker (AST-first spine; see ARCHITECTURE.md).

    A LOWER shared module (imports ONLY GoAst, below GoSafe): it owns [ptype] (the structural, constant-aware
    TYPE-CATEGORY assignment [GExpr -> option PTy]), its numeric/conversion combinators, and the
    value-position validity wrapper [svalue] — so the supportedness gate has ONE type authority:
      • GoSafe (ABOVE) reuses it for [SupportedProgram] — a free identifier / a closed type-error is
        rejected because [ptype] rejects it; the regressions that PIN those rejections live in GoSafe.
      • A future GoSem (the planned behavioral semantics, also above GoTypes) should reuse [svalue]
        (e.g. as the value-position gate for a blank-assign [_ = e]) rather than fork its own type-blind
        predicate — keeping ONE type authority across the layers.
    GoTypes has NO theorems (only [Definition]s / one [Inductive]), so it introduces NO axioms; the
    pre-commit all-[.v] axiom scan covers it.
    ============================================================================ *)
From Fido Require Import GoAst.   (* GoAst supplies the syntax ([GExpr]/[GoTy]/[BinOp]/…) AND [classify]
                                     (the keyword -> [GoTy] map for scalar conversions).  DELIBERATELY the
                                     ONLY Fido import — GoTypes is the bottom of the type-category layer. *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ===================================================================================================
    ===== TYPE-CATEGORY: ptype classifier (PTy + numeric/conversion combinators) =====
    =================================================================================================== *)

(** ---- A CONSTANT-AWARE STRUCTURAL TYPE-CATEGORY for the supported expression subset ([ptype]) ----
    The supportedness gate must NOT certify INVALID Go, so [ptype] is constant-aware, not shape-only: it
    REJECTS closed type / numeric / structural errors — float modulo or shift ([float64(1) % float64(2)],
    [float64(1) << 2]), constant overflow ([uint8(300)], [[]uint8{300}]), mixed fixed-width arithmetic
    ([int64(3) + int32(2)]), bool ordering ([(1==1) < (2==2)]), slice equality/ordering, [cap] of a string
    ([cap(string(x))]), invalid aggregate conversions ([chan int([]int{1})]), and — because Go's constant
    rules apply TRANSITIVELY through a conversion (a conversion of a constant is itself a typed CONSTANT) —
    const div / shift-by-zero and overflow that survive a conversion ([1 / int(0)], [1 << int(-1)],
    [uint8(int(300))], [uint8(float64(300))]).
    [ptype] assigns each expression a REFINED, CONSTANT-AWARE TYPE CATEGORY, or REJECTS it ([None]) as
    structurally ill-typed.  CONSTANTNESS SURVIVES conversions and constant binops: integers are split from
    floats and CONSTANTS from RUNTIME values; a constant carries its VALUE (a [Z]) — so representability/
    overflow and division/shift-by-zero are decided from the folded value at EVERY level — while a typed
    constant ALSO carries its [GoTy] (so mixed-width arithmetic and out-of-range typed-constant results are
    rejected) and a RUNTIME numeric carries only its [GoTy] (no value constraint — runtime conversions
    truncate, runtime div-by-zero is a panic not a compile error).  Aggregates ([PtAgg]) are a valid value but
    never numeric/printable.  ★SCOPE: in the no-declaration Program model a FREE identifier is UNDEFINED, so it
    is REJECTED ([ptype (EId _) = None] — its emitted Go would not compile); the ONLY admitted predeclared
    value-identifier is [nil] ([PtNil]), and it is admitted ONLY as a slice/chan conversion operand
    ([[]int(nil)] / [chan int(nil)]) — never as a bare value, an arithmetic/comparison operand, or a
    [len]/[cap]/[print]/[println] argument.
    ★ANTI-REGRESSION INVARIANT — NO rule turns a constant category ([PtIntConst]/[PtTIntConst]/[PtFloatConst])
    into a runtime category ([PtRunInt]/[PtRunFloat]) while dropping the value: constantness is PRESERVED
    through every conversion/binop, or the form is REJECTED.  (Conversions of a runtime operand DO yield a
    runtime category — but there was never a value to drop.)
    ★POSTURE — [ptype] is a CONSERVATIVE SUPPORTED-SUBSET classifier, NOT Go's typechecker; it is NOT proven
    complete or sound (there is no [ptype]-vs-Go-typechecker theorem — that is GoSem's job), and makes NO claim
    to reject every invalid form.  It admits a SUBSET and REJECTS anything it cannot classify as clearly
    supported, so it over-rejects much VALID Go too (any conversion of a KNOWN aggregate, [string] of a typed
    int, const+typed when not representable, nested-aggregate elements, float-CONSTANT arithmetic,
    platform-[uint] complement, an untyped const whose default-[int] value overflows, a not-exactly-
    representable const->float).  The closed-invalid CLASSES it is known to reject are PINNED by GoSafe's
    regressions (each added when found).  Because a FREE identifier is REJECTED (the no-declaration model
    has no variable bindings, so a bare [x] is undefined and its Go would not compile), the gate admits NO
    free-identifier form: the sole predeclared value-ident, [nil] ([PtNil]), is admitted only inside a
    slice/chan conversion. *)
Inductive PTy : Type :=
  | PtIntConst   (z : Z)            (* an UNTYPED INTEGER CONSTANT — value known, type not yet fixed (adapts on use) *)
  | PtTIntConst  (t : GoTy) (z : Z) (* a TYPED INTEGER CONSTANT of int-type [t], value [z] (from converting a const to [t]) *)
  | PtFloatConst (t : GoTy) (z : Z) (* a TYPED FLOAT CONSTANT (t = GTFloat64/GTFloat32), value the INTEGER [z] it came from *)
  | PtRunInt     (t : GoTy)         (* a RUNTIME (non-constant) integer of type [t] (e.g. [int(x)], [len([]int{..})] — note [len] of a STRING CONSTANT folds to [PtIntConst], NOT this) *)
  | PtRunFloat   (t : GoTy)         (* a RUNTIME (non-constant) float of type [t] (e.g. [float64(x)]) *)
  | PtBool
  | PtStr
  | PtAgg    (* a slice/chan aggregate value: a valid VALUE, but never numeric / order-comparable / printable *)
  | PtNil.   (* the predeclared value-identifier [nil] — admitted ONLY as a slice/chan conversion operand ([[]T(nil)]) *)

(** ---- numeric-type predicates over [GoTy] (the scalar numeric constructors) ---- *)
Definition is_int_goty (t : GoTy) : bool :=
  match t with
  | GTInt | GTInt64 | GTUint | GTU8 | GTI8 | GTU16 | GTI16 | GTU32 | GTI32 | GTU64 => true
  | _ => false
  end.
Definition is_float_goty (t : GoTy) : bool :=
  match t with GTFloat64 | GTFloat32 => true | _ => false end.
(** Decidable equality on the numeric SCALAR [GoTy]s (the [t] every typed-numeric category — [PtTIntConst] /
    [PtFloatConst] / [PtRunInt] / [PtRunFloat] — carries).  Total: any pair of DIFFERENT (or non-numeric)
    constructors is [false].  Used to forbid mixed-width arithmetic/comparison/assignment. *)
Definition numty_eqb (a b : GoTy) : bool :=
  match a, b with
  | GTInt, GTInt | GTInt64, GTInt64 | GTUint, GTUint
  | GTU8, GTU8 | GTI8, GTI8 | GTU16, GTU16 | GTI16, GTI16
  | GTU32, GTU32 | GTI32, GTI32 | GTU64, GTU64
  | GTFloat64, GTFloat64 | GTFloat32, GTFloat32 => true
  | _, _ => false
  end.

(** ===================================================================================================
    ===== CONST: representability / folding (the constant sub-layer ptype consults) =====
    Pure value→type-range / exact-interval / complement-fold helpers — no [PTy], no scope.  (A few sibling
    const helpers — [is_zero_const] / [is_neg_const] / [complement_const] — are kept inline beside the
    combinators that consume them, below.)
    =================================================================================================== *)

(** ---- INTEGER-CONSTANT REPRESENTABILITY ---- the inclusive value range of each fixed-width integer type;
    the PLATFORM types [int]/[uint] use the CONSERVATIVE 32-bit range, so a certified constant is in range on
    EVERY Go target (a 64-bit-only constant is rejected — sound on all platforms). *)
Definition int_ty_range (t : GoTy) : option (Z * Z) :=
  match t with
  | GTU8    => Some (0, 255)%Z
  | GTI8    => Some (-128, 127)%Z
  | GTU16   => Some (0, 65535)%Z
  | GTI16   => Some (-32768, 32767)%Z
  | GTU32   => Some (0, 4294967295)%Z
  | GTI32   => Some (-2147483648, 2147483647)%Z
  | GTU64   => Some (0, 18446744073709551615)%Z
  | GTInt64 => Some (-9223372036854775808, 9223372036854775807)%Z
  | GTInt   => Some (-2147483648, 2147483647)%Z     (* platform int: conservative 32-bit *)
  | GTUint  => Some (0, 4294967295)%Z               (* platform uint: conservative 32-bit *)
  | _ => None
  end.
Definition int_const_repr (z : Z) (t : GoTy) : bool :=
  match int_ty_range t with Some (lo, hi) => andb (Z.leb lo z) (Z.leb z hi) | None => false end.
(** A CONSERVATIVE SUFFICIENT test (NOT "iff exactly representable") that an int constant [z] is an EXACT
    constant of float type [t]: is [z] in the CONTIGUOUS interval [[-2^53, 2^53]] for [float64] ([[-2^24, 2^24]]
    for [float32]) where EVERY integer is exactly representable?  (There ARE exactly-representable integers
    OUTSIDE this interval — e.g. [2^60] is an exact [float64] — but they are NON-contiguous: an outside-interval
    integer MAY be exact OR rounded, and we do NOT model that sparse exactness/round-to-even relation.)  This is
    what we need: INSIDE the interval [z] is guaranteed the TRUE value, so a later float->int range-check on the
    carried [z] is sound.  OUTSIDE it we cannot guarantee [z] is the true value, so we conservatively REJECT the
    const->float conversion (rather than risk carrying a rounded lie) — for ANY outside-interval constant,
    whether or not it happens to be exact.  One such rejected case is a ROUNDED overflow,
    [int64(float64(9223372036854775807))]: the float64 rounds maxint64 UP to 2^63, which overflows [int64]. *)
Definition float_contig_exact_max (t : GoTy) : option Z :=
  match t with
  | GTFloat64 => Some 9007199254740992%Z    (* 2^53 *)
  | GTFloat32 => Some 16777216%Z            (* 2^24 *)
  | _ => None
  end.
Definition int_in_float_exact_interval (t : GoTy) (z : Z) : bool :=
  match float_contig_exact_max t with Some m => andb (Z.leb (Z.opp m) z) (Z.leb z m) | None => false end.

(** ===================================================================================================
    ===== TYPE-CATEGORY (cont.): category predicates + binop / comparison / conversion combinators =====
    =================================================================================================== *)

(** ---- numeric CATEGORY predicates ---- (a free identifier never reaches these — [ptype]'s [EId] case
    rejects it, so an INTEGER op requires a concrete integer category and a BOOL op a concrete bool.) *)
Definition is_int_cat   (c : PTy) : bool :=
  match c with PtIntConst _ | PtTIntConst _ _ | PtRunInt _ => true | _ => false end.
Definition is_float_cat (c : PTy) : bool :=
  match c with PtFloatConst _ _ | PtRunFloat _ => true | _ => false end.
Definition is_num_cat   (c : PTy) : bool := orb (is_int_cat c) (is_float_cat c).
Definition is_bool_cat  (c : PTy) : bool := match c with PtBool => true | _ => false end.
(** Extract the VALUE of an integer constant (untyped OR typed) — [None] for a non-int-const category.  The
    single authority for the const-zero / const-negative / shift-count / fold readers, so a TYPED int constant
    ([int(0)], [int(-1)]) is treated exactly like an untyped one (the constant rules apply transitively). *)
Definition int_const_val (c : PTy) : option Z :=
  match c with PtIntConst z | PtTIntConst _ z => Some z | _ => None end.

(** NUMERIC COMPARABILITY — single authority for numeric-comparison ([==]/[!=]/[<]/…) operand checking: can
    two numeric categories be compared?  Two int constants always compare; an int const compares with a
    typed/runtime int iff REPRESENTABLE in it (so [int8(1) == 300] is rejected); two typed/runtime ints compare
    iff SAME type (so [int32 == int64] is rejected); float CONSTANTS carry their type so [float64(1)==float32(1)]
    is rejected while [float64(1)==float64(x)] passes.  Conservatively, a CROSS int/float comparison
    ([int(1)==float64(1)], even when one side is an untyped const) is REJECTED — sound, and not needed by any
    positive.  bool/str/agg are handled by [eq_comparable]/[ord_comparable], not here. *)
Definition num_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  (* integer family *)
  | PtIntConst _, PtIntConst _ => true
  | PtIntConst z, PtTIntConst t _ | PtTIntConst t _, PtIntConst z => int_const_repr z t
  | PtIntConst z, PtRunInt t | PtRunInt t, PtIntConst z => int_const_repr z t
  | PtTIntConst t1 _, PtTIntConst t2 _ => numty_eqb t1 t2
  | PtTIntConst t1 _, PtRunInt t2 | PtRunInt t2, PtTIntConst t1 _ => numty_eqb t1 t2
  | PtRunInt t1, PtRunInt t2 => numty_eqb t1 t2
  (* float family (float constants carry their type) *)
  | PtFloatConst t1 _, PtFloatConst t2 _ => numty_eqb t1 t2
  | PtFloatConst t1 _, PtRunFloat t2 | PtRunFloat t2, PtFloatConst t1 _ => numty_eqb t1 t2
  | PtRunFloat t1, PtRunFloat t2 => numty_eqb t1 t2
  | _, _ => false
  end.

(** ARITHMETIC COMBINATION — single authority for the value-following binops [+ - * / % & | ^ &^] (the SHIFTS
    are separate: their count is independent).  [fold] computes the VALUE for the constant*constant cases; the
    result CATEGORY preserves constness:
    - both UNTYPED int consts -> a new UNTYPED int const (ARBITRARY PRECISION — no overflow until used);
    - untyped const + TYPED int const -> a TYPED const, with the FOLDED RESULT representability-checked in the
      type (so [int8(100)+int8(100)] = 200 -> REJECT) — and likewise typed+typed of the SAME type (DIFFERENT
      types REJECT: mixed width [int64(3)+int32(2)]);
    - a const combined with a RUNTIME int -> a runtime int of that type (the const must be REPRESENTABLE in /
      of the SAME type as the runtime), value no longer tracked (there is a runtime operand, so no fold);
    - runtime + runtime int -> same type;  runtime FLOAT + runtime float (or + untyped int const repr-as-float)
      -> runtime float of that type;  any FLOAT CONSTANT operand -> REJECT (conservative — we do not track
      fractional values, and no positive needs constant-float arithmetic);
    - any non-numeric operand (bool/str/agg/nil) -> REJECT.
    Callers gate the INT-ONLY ops ([% & | ^ &^] and the shifts) with [is_int_cat] FIRST, so no float reaches
    those; [num_arith] still rejects float-const + the [/]-zero check is done by the caller. *)
Definition num_arith (fold : Z -> Z -> Z) (cl cr : PTy) : option PTy :=
  match cl, cr with
  (* both UNTYPED int consts: arbitrary-precision fold *)
  | PtIntConst a, PtIntConst b => Some (PtIntConst (fold a b))
  (* untyped int const + typed int const: typed const, repr-check the FOLDED RESULT *)
  | PtIntConst a, PtTIntConst t b | PtTIntConst t b, PtIntConst a =>
      let r := fold a b in if int_const_repr r t then Some (PtTIntConst t r) else None
  (* typed int const + typed int const: SAME type, repr-check the result; DIFFERENT type -> reject *)
  | PtTIntConst t1 a, PtTIntConst t2 b =>
      if numty_eqb t1 t2 then let r := fold a b in if int_const_repr r t1 then Some (PtTIntConst t1 r) else None
      else None
  (* untyped int const + runtime int: const must be REPRESENTABLE in the runtime's type -> runtime int *)
  | PtIntConst a, PtRunInt t | PtRunInt t, PtIntConst a =>
      if int_const_repr a t then Some (PtRunInt t) else None
  (* typed int const + runtime int: SAME type -> runtime int *)
  | PtTIntConst t1 _, PtRunInt t2 | PtRunInt t2, PtTIntConst t1 _ =>
      if numty_eqb t1 t2 then Some (PtRunInt t2) else None
  (* runtime int + runtime int: SAME type *)
  | PtRunInt t1, PtRunInt t2 => if numty_eqb t1 t2 then Some (PtRunInt t1) else None
  (* runtime float + runtime float: SAME type *)
  | PtRunFloat t1, PtRunFloat t2 => if numty_eqb t1 t2 then Some (PtRunFloat t1) else None
  (* runtime float + untyped int const (repr-as-float): runtime float of that type *)
  | PtRunFloat t, PtIntConst z | PtIntConst z, PtRunFloat t =>
      if int_in_float_exact_interval t z then Some (PtRunFloat t) else None
  (* any FLOAT CONSTANT operand, or any other mix (bool/str/agg) -> REJECT *)
  | _, _ => None
  end.

(** A divisor that is a CONSTANT (untyped int, typed int, OR typed FLOAT) ZERO — the constant rules apply
    transitively, so [int(0)] (a typed const 0) and [float64(0)] (a typed float const 0) BOTH count like [0]:
    Go rejects constant division by zero for floats too ("division by zero").  A RUNTIME / deferred divisor is
    NOT a constant zero (runtime div-by-zero is a panic, not a compile error — GoSem's concern).  [is_neg_const]
    (shift counts) stays INT-only — shifts gate out floats before reaching it. *)
Definition is_zero_const (c : PTy) : bool :=
  match c with
  | PtIntConst z | PtTIntConst _ z | PtFloatConst _ z => Z.eqb z 0   (* incl. a typed FLOAT zero [float64(0)] *)
  | _ => false
  end.
Definition is_neg_const  (c : PTy) : bool := match int_const_val c with Some z => Z.ltb z 0 | None => false end.

(** THE NUMERIC BINOP TYPE-CHECKER — single authority for [* / % << >> & &^ + - | ^].  Enforces, structurally:
    - [%], [&], [|], [^], [&^] and the shifts require INTEGER operands (a FLOAT operand — const or runtime —
      is rejected by the [is_int_cat] gate, closing [float64(1) % float64(2)] / [float64(1) << 2]);
    - [/] and [%] reject a CONSTANT-ZERO divisor (incl. a TYPED const zero [int(0)] and one folded from a
      constant subexpression, [1/(int(1)-int(1))]);
    - the shifts reject a NEGATIVE constant shift count ([1 << int(-1)], [1 << (-1)]) and let the count type be
      independent of the left type; the result takes the LEFT operand's type AND constness (a typed-const left
      shifted by a const count FOLDS, with the result repr-checked in the type);
    - all other forms combine via [num_arith], which folds constants (preserving constness) and repr-checks
      typed-constant results so [int8(100)+int8(100)] is rejected. *)
Definition shfold (o : BinOp) (a b : Z) : Z := match o with BShl => Z.shiftl a b | _ => Z.shiftr a b end.
Definition num_binop (o : BinOp) (cl cr : PTy) : option PTy :=
  match o with
  | BAdd => num_arith Z.add cl cr
  | BSub => num_arith Z.sub cl cr
  | BMul => num_arith Z.mul cl cr
  | BDiv => if is_zero_const cr then None else num_arith Z.quot cl cr
  | BRem =>
      if andb (is_int_cat cl) (is_int_cat cr) then
        if is_zero_const cr then None else num_arith Z.rem cl cr
      else None
  | BAnd    => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.land cl cr else None
  | BOr     => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.lor  cl cr else None
  | BXor    => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.lxor cl cr else None
  | BAndNot => if andb (is_int_cat cl) (is_int_cat cr)
               then num_arith (fun a b => Z.land a (Z.lnot b)) cl cr else None
  | BShl | BShr =>
      if andb (is_int_cat cl) (is_int_cat cr) then
        if is_neg_const cr then None
        else match cl with
             | PtIntConst a =>
                 match int_const_val cr with
                 | Some b => Some (PtIntConst (shfold o a b))   (* both const -> untyped const fold *)
                 | None   => Some (PtRunInt GTInt)              (* 1 << x : the untyped 1 defaults to int *)
                 end
             | PtTIntConst t a =>
                 match int_const_val cr with
                 | Some b => let r := shfold o a b in if int_const_repr r t then Some (PtTIntConst t r) else None
                 | None   => Some (PtRunInt t)                  (* int8(1) << x : runtime, keeps the type *)
                 end
             | PtRunInt t => Some (PtRunInt t)
             | _ => None                                        (* floats already excluded by the gate *)
             end
      else None
  | _ => None    (* the comparison / logical binops are not numeric — handled in [ptype] *)
  end.

(** EQUALITY ([==]/[!=]) operand check: COMPARABLE + mutually compatible.  Comparable = numeric / string /
    bool — NOT [PtAgg] (slice/map/func equality is rejected) and NOT [PtNil] (a bare [nil == nil] is rejected;
    a free ident, the only thing a slice could be compared against, is itself rejected at [ptype]).  Numeric
    equality reuses [num_comparable] (so [int32 == int64] is rejected). *)
Definition eq_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtBool, PtBool => true
  | PtStr, PtStr => true
  | _, _ => num_comparable cl cr
  end.
(** ORDERING ([<]/[<=]/[>]/[>=]) operand check: ORDERED + mutually compatible.  Ordered = numeric / string —
    NOT bool (so [(1==1) < (2==2)] is rejected) and NOT [PtAgg]/[PtNil] (slice / nil ordering rejected). *)
Definition ord_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtStr, PtStr => true
  | _, _ => num_comparable cl cr
  end.

(** SCALAR CONVERSION [T(a)] type-checker, for a scalar type keyword [T] (its [GoTy] via [classify]).  ★The
    KEY constant-aware rule: in Go a conversion of a CONSTANT is itself a TYPED CONSTANT, so the constant rules
    apply TRANSITIVELY — constness must SURVIVE the conversion (so [1/int(0)], [uint8(int(300))],
    [uint8(float64(300))] are REJECTED, not silently dropped to a runtime category).  So:
    - [bool(a)] needs a bool source;
    - [string(a)] a string source (or a rune-representable int CONSTANT, untyped or typed — NOT an arbitrary
      runtime int, conservative);
    - a NUMERIC target with a CONSTANT source ([PtIntConst]/[PtTIntConst]/[PtFloatConst]) yields a TYPED
      CONSTANT, with the carried VALUE [z] REPRESENTABILITY-CHECKED against [T] (to an int type -> [PtTIntConst
      T z], to a float type -> [PtFloatConst T z]).  This rejects [uint8(300)], [uint8(int(300))],
      [uint8(float64(300))], [int8(128)].  A float->int constant conversion is sound because a [PtFloatConst]
      is BUILT only when the source integer is within the float's CONTIGUOUS exact interval
      ([int_in_float_exact_interval] — [|z|<=2^53]/[2^24], a CONSERVATIVE SUFFICIENT test; a constant outside it
      is REJECTED at the const->float step, never carried as a rounded lie), so its carried [z] is the true value
      and the later int range-check is exact;
    - a NUMERIC target with a RUNTIME source ([PtRunInt]/[PtRunFloat]) yields a RUNTIME value (runtime
      conversions truncate/round and are valid — NO representability constraint), so [int64(len([]int{1}))],
      [uint8(len([]int{1}))] (whose inner [len …] is a runtime int) stay admitted; (a runtime source can only
      arise from [len]/[cap] of an aggregate now — a FREE ident like [x] is rejected upstream at [ptype]);
    - bool/string/aggregate/nil sources to a numeric target are rejected (so [int([]int{1})] / [int(true)] /
      [int(nil)] fail). *)
Definition conv_to_scalar (ca : PTy) (t : GoTy) : option PTy :=
  match t with
  | GTBool => match ca with PtBool => Some PtBool | _ => None end
  | GTString =>
      match ca with
      | PtStr => Some PtStr
      | PtIntConst z | PtTIntConst _ z =>
          if int_const_repr z GTI32 then Some PtStr else None   (* string(rune const) *)
      | _ => None
      end
  | GTFloat64 | GTFloat32 =>
      match ca with
      | PtIntConst z | PtTIntConst _ z | PtFloatConst _ z =>      (* CONSTANT source -> typed float const (EXACT only) *)
          if int_in_float_exact_interval t z then Some (PtFloatConst t z) else None
      | PtRunInt _ | PtRunFloat _ => Some (PtRunFloat t)         (* RUNTIME source -> runtime float *)
      | _ => None
      end
  | GTInt | GTInt64 | GTUint | GTU8 | GTI8 | GTU16 | GTI16 | GTU32 | GTI32 | GTU64 =>
      match ca with
      | PtIntConst z | PtTIntConst _ z | PtFloatConst _ z =>      (* CONSTANT source -> typed int const, repr-checked *)
          if int_const_repr z t then Some (PtTIntConst t z) else None
      | PtRunInt _ | PtRunFloat _ => Some (PtRunInt t)           (* RUNTIME source -> runtime int *)
      | _ => None
      end
  | _ => None   (* [classify] yields only scalar keyword GoTys here; defensive *)
  end.

(** ASSIGNABILITY of a value CATEGORY to a declared element/target [GoTy] — single authority for composite
    literal elements.  An UNTYPED int CONSTANT is assignable to any numeric type it is REPRESENTABLE in (so
    [[]uint8{300}] is rejected, [[]float64{1}] accepted); a TYPED constant or RUNTIME numeric only to its OWN
    type (so [[]int{int64(1)}] and [[]uint8{int(300)}] are rejected — a typed constant is NOT untyped, its type
    must match exactly); bool/string to their type; an aggregate or [nil] element is conservatively rejected
    (no free ident reaches here — it is rejected at [ptype]). *)
Definition assignable_to_ty (ce : PTy) (t : GoTy) : bool :=
  match ce with
  | PtIntConst z =>
      if is_int_goty t then int_const_repr z t
      else if is_float_goty t then int_in_float_exact_interval t z
      else false
  | PtTIntConst t' _ | PtRunInt t' => if is_int_goty t then numty_eqb t' t else false
  | PtFloatConst t' _ | PtRunFloat t' => if is_float_goty t then numty_eqb t' t else false
  | PtBool => match t with GTBool => true | _ => false end
  | PtStr  => match t with GTString => true | _ => false end
  | PtAgg | PtNil => false
  end.

(** The bitwise-complement VALUE of a typed integer constant [z] of type [t] — [None] when it CANNOT be folded
    SOUNDLY.  For a FIXED-WIDTH UNSIGNED type the complement is [(2^w - 1) - z] (= flip all [w] bits), exact
    because [w] is fixed (so [^uint8(0) = 255], not the naive [Z.lnot 0 = -1]); for a SIGNED type it is
    [Z.lnot z = -z-1], which is WIDTH-INDEPENDENT (so platform [int] is fine).  ★The platform UNSIGNED type
    [GTUint] returns [None] — its complement [2^w - 1 - z] is PLATFORM-WIDTH-dependent (2^32-1 on a 32-bit
    target, 2^64-1 on 64-bit), so there is NO single sound value to fold; sealing it HERE (not at the caller)
    makes the unsound value structurally impossible to produce.  Deliberately does NOT consult [int_ty_range]
    (whose [GTUint] entry is the conservative 32-bit range — correct for a TARGET repr-check, but the WRONG
    width to fold a complement against). *)
Definition complement_const (t : GoTy) (z : Z) : option Z :=
  match t with
  | GTU8  => Some (255 - z)%Z
  | GTU16 => Some (65535 - z)%Z
  | GTU32 => Some (4294967295 - z)%Z
  | GTU64 => Some (18446744073709551615 - z)%Z
  | GTI8 | GTI16 | GTI32 | GTInt | GTInt64 => Some (Z.lnot z)   (* signed: -z-1 is width-independent *)
  | GTUint => None        (* platform unsigned: 2^w-1-z is platform-width-dependent — NO sound fold *)
  | _ => None             (* non-integer type *)
  end.

(** ===================================================================================================
    ===== SCOPE: identifier admissibility (nil only; free idents rejected) =====
    The scope rule is realized HERE in [ptype]'s [EId] case (and in [svalue]'s [PtNil] rejection below): the
    no-declaration Program model has no variable bindings, so a FREE identifier is UNDEFINED and its emitted Go
    would not compile.  [ptype (EId i)] therefore returns a category ONLY for the predeclared value-identifier
    [nil] (-> [PtNil]); EVERY other identifier is REJECTED ([None]).  [PtNil] is admitted ONLY as a slice/chan
    conversion operand (the [EConv] case) and nowhere else.
    =================================================================================================== *)

(** ★INVARIANT — [ptype] is NOT Go's typechecker; it is a CONSERVATIVE supported-subset classifier.  No new
    rule may be added to it unless it (a) REJECTS a real CLOSED bad program currently accepted, or (b) ADMITS a
    needed supported demo intentionally.  (This is the standing tightening discipline — grow the certificate's
    HONESTY, not its surface area.)
    [ptype]: the structural TYPE-CATEGORY assignment.  [None] = structurally ill-typed / out-of-scope
    (rejected). *)
Fixpoint ptype (e : GExpr) : option PTy :=
  match e with
  | EId i => if String.eqb (proj1_sig i) "nil" then Some PtNil else None   (* SCOPE: only the predeclared [nil]; every other ident is undefined -> rejected *)
  | EInt z => Some (PtIntConst z)
  | EHex zc => Some (PtIntConst (proj1_sig zc))   (* a hex literal IS an integer constant (non-negative; same category as [EInt]) *)
  | EStr _ => Some PtStr   (* a string literal is the printable SCALAR string category *)
  | EBn o l r =>
      match ptype l, ptype r with
      | Some cl, Some cr =>
          match o with
          | BAdd => match cl, cr with
                    | PtStr, PtStr => Some PtStr   (* string CONCATENATION ["a" + "b"] — a string (valid Go); the result is a [PtStr] (no const value tracked, so [len] of it stays rejected, like any non-literal string) *)
                    | _, _ => num_binop o cl cr    (* numeric add — and a MIXED string/number is REJECTED ([num_binop] gives [None] on a non-numeric operand) *)
                    end
          | BMul|BDiv|BRem|BShl|BShr|BAnd|BAndNot|BSub|BOr|BXor => num_binop o cl cr
          | BEq|BNe => if eq_comparable cl cr then Some PtBool else None
          | BLt|BLe|BGt|BGe => if ord_comparable cl cr then Some PtBool else None
          | BLAnd|BLOr => if andb (is_bool_cat cl) (is_bool_cat cr) then Some PtBool else None
          end
      | _, _ => None
      end
  | EUn o e0 =>
      match ptype e0 with
      | Some c =>
          match o with
          | UNeg => match c with                              (* unary minus: int or float; const FOLDS (constness kept) *)
                    | PtIntConst z => Some (PtIntConst (Z.opp z))
                    | PtTIntConst t z =>                       (* -int8(-128) = 128 -> overflow -> reject *)
                        let r := Z.opp z in if int_const_repr r t then Some (PtTIntConst t r) else None
                    | PtFloatConst t z => Some (PtFloatConst t (Z.opp z))
                    | PtRunInt t => Some (PtRunInt t) | PtRunFloat t => Some (PtRunFloat t)
                    | _ => None end
          | UXor => match c with                              (* bitwise complement: INTEGER only (no float); const FOLDS *)
                    | PtIntConst z => Some (PtIntConst (Z.lnot z))
                    | PtTIntConst t z =>                       (* [complement_const] seals platform-[uint] -> None internally *)
                        match complement_const t z with
                        | Some r => if int_const_repr r t then Some (PtTIntConst t r) else None
                        | None => None
                        end
                    | PtRunInt t => Some (PtRunInt t)
                    | _ => None end
          | UNot => match c with PtBool => Some PtBool | _ => None end
          | UDeref | UAddr => None
          end
      | None => None
      end
  | ECall (EId i) (a :: nil) =>
      let fn := proj1_sig i in
      match ptype a with
      | None => None
      | Some ca =>
          if String.eqb fn "len"
          then match a, ca with
               | EStr s, _ => Some (PtIntConst (Z.of_nat (String.length s)))   (* [len] of a STRING CONSTANT is itself a CONSTANT (its byte count) — Go folds it; modelling it as a runtime int would wrongly certify e.g. [int8(len("..")+200)] (a const-202->int8 overflow Go REJECTS) *)
               | _, PtAgg => Some (PtRunInt GTInt)                             (* [len] of a slice/aggregate: a runtime int (slices/maps are not constants) *)
               | _, _ => None end                                             (* a non-literal string ([string(x)]…): cannot soundly fold its length here — reject (fail-loud) *)
          else if String.eqb fn "cap"
          then match ca with PtAgg => Some (PtRunInt GTInt) | _ => None end          (* cap: aggregate ONLY (NOT string) *)
          else match classify fn with
               | Some t => conv_to_scalar ca t                                              (* a scalar conversion T(a) *)
               | None => None                                                               (* unknown function: REJECT *)
               end
      end
  | ECall _ _ => None
  | EConv c e0 =>
      match c with
      | CTMap _ _ => None                 (* a MAP conversion is QUARANTINED (key-type comparability not structural) *)
      | CTSlice _ | CTChan _ =>
          (* an aggregate conversion is admitted ONLY for the predeclared [nil] operand ([[]int(nil)]); a KNOWN
             aggregate/scalar operand — or a free ident (now rejected upstream) — is REJECTED
             ([chan int([]int{1})], mismatched conversions) *)
          match ptype e0 with Some PtNil => Some PtAgg | _ => None end
      end
  | ESliceLit t es =>
      if forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es
      then Some PtAgg else None
  | EMapLit _ _ _ => None                 (* a MAP literal is QUARANTINED (comparable-key TYPE + assignability not structural) *)
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => None
  end.

(** STRUCTURALLY-supported VALUE expression — [ptype] accepts it (well-typed by REFINED category).  So a closed
    type-error is REJECTED — not just the shape errors ([len(1)] / [1 && 2] / [int([]int{1})] / [map[..]..{..}])
    but the numeric/structural ones too ([float64(1) % float64(2)], [uint8(300)], [uint8(int(300))], [1/int(0)],
    [int64(3)+int32(2)], slice/bool comparison, [cap(string(x))], [chan int([]int{1})]) — AND, now, FREE
    identifiers (a bare [x] is undefined in the no-declaration model — [ptype (EId _) = None]).  Accepted: [EInt],
    well-typed binops/unops/conversions, [len] of a string LITERAL (folds to the constant byte count) or of an
    aggregate (a runtime int), [cap] of an aggregate, and a slice literal whose elements are ASSIGNABLE to its
    element type.  ([len] of a NON-literal string — e.g. [len(string(65))] — is REJECTED: its const byte-length
    is not folded here.)  ★[PtNil] (the predeclared [nil]) is NOT a value:
    a bare [_ = nil] is "use of untyped nil" (invalid) — [svalue (EId "nil") = false]; [nil] is a value ONLY
    inside a slice/chan conversion ([[]int(nil)], which [ptype] gives [PtAgg]).  ★UNTYPED-CONSTANT DEFAULT-[int]
    BOUNDARY: where a bare UNTYPED int constant is USED as a value (e.g. [_ = <untyped const>], or
    [panic(<untyped const>)] whose [interface{}] arg fixes the default type), Go gives it the default type [int]
    — so the value must FIT in [int].  We require it fit the CONSERVATIVE 32-bit range (sound on every Go target),
    so [_ = <a 40-bit const>] is REJECTED while [_ = 1] is admitted.  (A TYPED constant [PtTIntConst] was already
    range-checked at its conversion.) *)
Definition svalue (e : GExpr) : bool :=
  match ptype e with
  | Some (PtIntConst z) => int_const_repr z GTInt   (* default-[int] boundary: bare untyped const must fit int *)
  | Some PtNil => false   (* a bare [nil] value is "use of untyped nil" — invalid; [nil] is a value only inside a conversion *)
  | Some _ => true
  | None => false
  end.
