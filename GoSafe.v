(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; see ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate — a supported-subset check — NOT behavioral safety, and it
    is NAMED so deliberately (naming is a correctness claim: never call a syntactic gate "Safe").  The
    semantic [BehaviorSafe] (no nil-deref / OOB / send-on-closed / illegal-close / data-race / …, defined over
    GoSem) lands once GoSem is the ONE authoritative semantics — at which point the blessed path becomes
    emit_safe over a [SafeProgram] (= EmittableProgram + BehaviorSafe).  Until then GoEmit emits only the
    SUPPORTED subset via emit_supported, and must NOT be described as behaviorally safe.
    ============================================================================ *)
From Fido Require Import GoAst.   (* GoAst supplies the syntax AND [classify] (the keyword -> GoTy map for scalar
                                     conversions).  DELIBERATELY NOT GoPrint — the SAFETY layer must NOT depend on
                                     the printer (ARCHITECTURE.md §2: GoAst -> GoPrint and GoAst -> GoSafe are
                                     SIBLINGS off GoAst, not a chain through the printer). *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ===================================================================================================
    ===== TYPE-CATEGORY: ptype classifier (PTy + numeric/conversion combinators) =====
    =================================================================================================== *)

(** ---- A CONSTANT-AWARE STRUCTURAL TYPE-CATEGORY for the supported expression subset ([ptype]) ----
    The supportedness gate must NOT certify INVALID Go.  A purely shape-based [svalue] leaked TYPE side
    conditions; an under-refined [ptype] (a single fat [PtNum] / a single comparison rule / a shared
    [len]=[cap] rule / a shape-only aggregate conversion) STILL leaked numeric and structural side conditions:
    float modulo / float shift ([float64(1) % float64(2)], [float64(1) << 2]), constant overflow
    ([uint8(300)], [[]uint8{300}]), mixed fixed-width arithmetic ([int64(3) + int32(2)]), bool ordering
    ([(1==1) < (2==2)]), slice equality/ordering, [cap] of a string ([cap(string(x))]), and invalid aggregate
    conversions ([chan int([]int{1})]) all sailed through.  A LATER gap (Codex stop-review): a numeric
    CONVERSION ERASED the constant's value ([conv_to_scalar] mapped [PtIntConst z] -> [PtInt t]), so a typed
    constant lost its constness — and Go's constant rules apply TRANSITIVELY through conversions (a conversion
    of a constant is itself a typed CONSTANT), so [1 / int(0)], [1 << int(-1)], [uint8(int(300))],
    [uint8(float64(300))] (all CLOSED compile errors) sailed through.
    [ptype] now assigns each expression a REFINED, CONSTANT-AWARE TYPE CATEGORY, or REJECTS it ([None]) as
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
    ★POSTURE (NOT a proven completeness theorem — there is no [ptype]-vs-Go-typechecker proof; that is GoSem):
    [ptype] is a MAXIMALLY-CONSERVATIVE BEST-EFFORT checker — it aims to reject EVERY closed form Go's type
    checker rejects, and it deliberately rejects much VALID Go too (any conversion of a KNOWN aggregate,
    [string] of a typed int, const+typed when not representable, nested-aggregate elements, float-CONSTANT
    arithmetic, platform-[uint] complement, an untyped const whose default-[int] value overflows, a
    not-exactly-representable const->float), which is the correct posture — a smaller subset that is sound on
    the classes covered.  The covered closed-invalid classes are PINNED by the regressions below (each new
    class Codex finds is added there).  Because a FREE identifier is now REJECTED (the no-declaration model has
    no variable bindings, so a bare [x] is undefined and its Go would not compile), the gate admits NO unproven
    free-identifier form: the sole predeclared value-ident, [nil] ([PtNil]), is admitted only inside a
    slice/chan conversion. *)
Inductive PTy : Type :=
  | PtIntConst   (z : Z)            (* an UNTYPED INTEGER CONSTANT — value known, type not yet fixed (adapts on use) *)
  | PtTIntConst  (t : GoTy) (z : Z) (* a TYPED INTEGER CONSTANT of int-type [t], value [z] (from converting a const to [t]) *)
  | PtFloatConst (t : GoTy) (z : Z) (* a TYPED FLOAT CONSTANT (t = GTFloat64/GTFloat32), value the INTEGER [z] it came from *)
  | PtRunInt     (t : GoTy)         (* a RUNTIME (non-constant) integer of type [t] (e.g. [int(x)], [len(x)]) *)
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
    apply TRANSITIVELY — constness must SURVIVE the conversion (the prior bug erased it: [PtIntConst z]->[PtInt
    t], so [1/int(0)], [uint8(int(300))], [uint8(float64(300))] sailed through).  So:
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
  | EStr _ => Some PtStr   (* a string literal is the printable SCALAR string category *)
  | EBn o l r =>
      match ptype l, ptype r with
      | Some cl, Some cr =>
          match o with
          | BMul|BDiv|BRem|BShl|BShr|BAnd|BAndNot|BAdd|BSub|BOr|BXor => num_binop o cl cr
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
          then match ca with PtStr | PtAgg => Some (PtRunInt GTInt) | _ => None end (* len: string OR aggregate *)
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
    well-typed binops/unops/conversions, [len] of a string-or-aggregate, [cap] of an aggregate, and a slice
    literal whose elements are ASSIGNABLE to its element type.  ★[PtNil] (the predeclared [nil]) is NOT a value:
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

(** ===================================================================================================
    ===== STRUCTURAL: statement-shape / supported-syntax (the [stmt_ok] / [supported_program] gate) =====
    =================================================================================================== *)

(** Is a builtin [f] valid as a standalone EXPRESSION-STATEMENT call, by NAME and ARITY only?  [println]/
    [print] are variadic in arg COUNT; [panic] takes exactly one.  This checks only name+arity — argument
    TYPES are checked SEPARATELY and per-builtin in [expr_stmt_ok] ([printable_arg_ok] for [print]/[println]
    — NOT "any type": only the guaranteed-printable SCALAR subset — and [svalue] for [panic], which takes an
    [interface{}]).  Deliberately EXACT for the current AST (no user funcs / imports yet).  Excluded on
    purpose: CONVERSIONS ([int(x)] is not a call) and VALUE-returning builtins ([len(x)]/… — "evaluated but
    not used" as a statement).  ([close]/[delete] add a channel/map arg-type constraint — deferred to GoSem.)
    Widens with user funcs / a symbol table. *)
Definition stmt_call_ok (f : string) (args : list GExpr) : bool :=
  if String.eqb f "println" then true                                  (* variadic in arg COUNT *)
  else if String.eqb f "print" then true                               (* variadic in arg COUNT *)
  else if String.eqb f "panic" then (match args with _ :: nil => true | _ => false end)  (* exactly 1 *)
  else false.

(** A [print]/[println] argument GUARANTEED-printable by the Go spec.  ★Go-spec NOTE (Bootstrapping): [print]/
    [println] are bootstrapping builtins whose implementations need NOT accept arbitrary argument types — only
    BOOLEAN, NUMERIC, and STRING are always supported.  So a printable arg is one [ptype] gives a SCALAR
    category (a numeric — [PtIntConst]/[PtTIntConst]/[PtFloatConst]/[PtRunInt]/[PtRunFloat] — or [PtBool]/
    [PtStr]).  This reuses the structural type-checker, so it INHERITS its rejection of closed type-errors —
    e.g. [len(1)] (an int is not len-able), [bool(1)], [1 && 2], [!1], [int([]int{1})], [float64(1) %
    float64(2)], [uint8(300)], [uint8(int(300))], [1/int(0)] — and of non-scalars ([PtAgg] slice/chan literals
    and conversions), of [nil] ([PtNil]), and of FREE identifiers (a bare [x] is undefined -> [ptype] [None]):
    emit a scalar value instead.  ([println(int64(3))] / [println(len([]int{1}))] stay admitted: a conversion of
    a constant / a [len] of an aggregate has a KNOWN scalar category.)  ★The default-[int] boundary applies: a
    bare UNTYPED int constant arg gets default type [int], so it must FIT in (conservative 32-bit) [int] —
    [println(1)] ✓, [println(<huge>)] REJECT (a TYPED constant was already range-checked at its conversion). *)
Definition printable_arg_ok (e : GExpr) : bool :=
  match ptype e with
  | Some (PtIntConst z) => int_const_repr z GTInt   (* default-[int] boundary: a bare untyped const must fit int *)
  | Some (PtTIntConst _ _) | Some (PtFloatConst _ _)
  | Some (PtRunInt _) | Some (PtRunFloat _) | Some PtBool | Some PtStr => true
  | _ => false
  end.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec a bare expression statement must be a
    CALL (a plain value [1] / [a + b] is "evaluated but not used"), AND — crucially — a genuine function call,
    NOT a CONVERSION ([int(x)] is a conversion, also invalid as a statement).  Since no user functions exist
    yet, the statement-valid callees are EXACTLY the whitelisted builtins at their correct arity
    ([stmt_call_ok]).  ARGUMENTS are checked PER BUILTIN: [print]/[println] admit only the guaranteed-printable
    SCALAR subset ([printable_arg_ok] — NOT arbitrary [svalue], so [println(<slice/map>)] / aggregate printing
    is excluded as implementation-defined); [panic] admits any [svalue] (it takes an [interface{}]).  So
    [int64(3)] / [Foo(x)] / [1()] / [len([]int{1})] / [panic()] / [println([]int{1})] / [panic(x)] (free [x]) as
    statements are all rejected; [println(int64(3))] / [println(1 + 2)] / [panic(1)] are accepted. *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall (EId f) args =>
      let fn := proj1_sig f in
      stmt_call_ok fn args &&
      (if String.eqb fn "panic" then forallb svalue args else forallb printable_arg_ok args)
  | _                  => false
  end.

(** A statement in the SUPPORTED subset: an expression statement must be [expr_stmt_ok]; a bare [return] is
    always fine (a valid tail of a void func like [main]); a VALUE return [return e] ([GsReturnVal]) is
    REJECTED — the only function we emit is [main], which is VOID, so `return <value>` is invalid Go ("too
    many return values").  (It becomes supported, conditional on the enclosing function's result type, once
    NON-void functions enter the AST — a clean demonstration that GoAst represents more than the gate admits.) *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e    => expr_stmt_ok e
  | GsReturn        => true
  | GsReturnVal _   => false   (* value return is invalid in the void [main] — the only function emitted today *)
  | GsBlankAssign e => svalue e  (* [_ = e] is valid iff [e] PRODUCES a value — so [_ = println(1)] (void) is rejected *)
  end.

(** PHASE-1 supportedness — DECIDABLE (bool-reflected): the program is a runnable `package main` whose body is
    entirely in the printer/emitter's STRUCTURALLY-supported statement subset (each statement is a [return] or
    a structurally-well-formed call expression statement).  It rejects the structural absurdities Go's grammar/
    statement rules forbid: a bare-value statement `func main(){ 1 }` ("evaluated but not used") and a call of a
    non-callable `func main(){ 1() }` are both [false], so no certificate exists and [emit_supported] can never
    print them.  SCOPE OF THE CLAIM (kept honest): this is CONSERVATIVE STRUCTURAL scope + type-category
    supportedness — it REJECTS a free (undefined) identifier (the current Program has NO declarations, so a free
    [x] could never compile) and a structurally-evident type/constant error, but it is NOT full Go type-checking
    or behavioral safety (the [BehaviorSafe]/GoSem layer, later).  So it is SUPPORTEDNESS, not "guaranteed-
    compiling" and not behavioral safety.  (The package-name-ONLY check was too weak — it certified invalid Go
    — now fixed.) *)
Definition supported_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main" && forallb stmt_ok (prog_body p).
Definition SupportedProgram (p : Program) : Prop := supported_program p = true.

(** REGRESSION (P0, external review 2026-06-28) — a bare-value expression statement `func main(){ 1 }` is NOT
    supported, so no certificate exists for it and the blessed emitter can NEVER print this invalid Go.  The
    [Example] pins [supported_program = false]; the [Fail] locks the gate: if a future change re-weakened
    [SupportedProgram], this [reflexivity] would START to succeed and the build would break right here. *)
Definition unsupported_value_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EInt 1)].
Example value_stmt_unsupported : supported_program unsupported_value_stmt = false.
Proof. reflexivity. Qed.
(* [Fail Example … := eq_refl] is a SINGLE vernac that must fail to typecheck: [eq_refl] cannot inhabit
   [SupportedProgram unsupported_value_stmt] (= [false = true]).  (Note: [Fail Lemma … . Proof. … Qed.] would
   NOT work — [Fail] guards only the goal-opening vernac, which always succeeds.) *)
Fail Example value_stmt_supported : SupportedProgram unsupported_value_stmt := eq_refl.

(** REGRESSION (gate coverage) — the PACKAGE-NAME half of [supported_program].  A non-`main` package, here
    `package lib` with an otherwise-FINE body ([return]), is NOT supported: [GoEmit] emits `package main` /
    `func main()` (no import block — rule 5), so a non-main package cannot be the emitted unit.  The body is
    deliberately supported, ISOLATING the package-name check (the statement-body half is pinned by the
    regressions above; this pins the conjunct they don't reach). *)
Definition unsupported_nonmain_pkg : Program :=
  mkProgram (mkIdent "lib" eq_refl) [GsReturn].
Example nonmain_pkg_unsupported : supported_program unsupported_nonmain_pkg = false.
Proof. reflexivity. Qed.
Fail Example nonmain_pkg_supported : SupportedProgram unsupported_nonmain_pkg := eq_refl.

(** REGRESSION (external review 2026-06-28, follow-up) — a CALL of a non-callable, `func main(){ 1() }`, is
    call-SHAPED but structurally invalid Go; [expr_stmt_ok] rejects it (the callee [EInt 1] is not an [EId]),
    so it is NOT supported and cannot be certified. *)
Definition unsupported_call_value : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EInt 1) nil)].
Example call_value_unsupported : supported_program unsupported_call_value = false.
Proof. reflexivity. Qed.
Fail Example call_value_supported : SupportedProgram unsupported_call_value := eq_refl.

(** REGRESSION (external review 2026-06-28, follow-up²) — a call of a type assertion, `func main(){ x.(int)() }`,
    is call-shaped but a type-assertion callee is not an [EId], so [expr_stmt_ok] rejects it (a concrete
    [x.(int)] is anyway concretely non-callable). NOT supported. *)
Definition unsupported_assert_call : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EAssert (EId (mkIdent "x" eq_refl)) GTInt) nil)].
Example assert_call_unsupported : supported_program unsupported_assert_call = false.
Proof. reflexivity. Qed.
Fail Example assert_call_supported : SupportedProgram unsupported_assert_call := eq_refl.

(** REGRESSION (external review 2026-06-28, follow-up³) — `func main(){ int(x) }` is identifier-call-SHAPED
    but [int] is a TYPE, so [int(x)] is a CONVERSION, not a call, and a conversion is NOT a valid expression
    statement ("evaluated but not used").  [int] is not accepted by [stmt_call_ok], so it is NOT supported. *)
Definition unsupported_conversion_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "int" eq_refl)) [EId (mkIdent "x" eq_refl)])].
Example conversion_stmt_unsupported : supported_program unsupported_conversion_stmt = false.
Proof. reflexivity. Qed.
Fail Example conversion_stmt_supported : SupportedProgram unsupported_conversion_stmt := eq_refl.

(** POSITIVE — a conversion IS fine in VALUE position: `func main(){ println(int64(3)) }` is supported (the
    statement is a [println] call; its argument [int64(3)] is a conversion of a CONSTANT, a valid [svalue]).
    This pins the value-vs-statement asymmetry the conversion-statement regression above relies on. *)
Definition supported_conv_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int64" eq_refl)) [EInt 3]])].
Example conv_arg_supported : SupportedProgram supported_conv_arg.
Proof. reflexivity. Qed.

(** TIGHTENING (external review 2026-06-29) — a conversion of a FREE identifier `func main(){ println(int(x)) }`
    is NOT supported: in the no-declaration model [x] is undefined, so [ptype (EId "x") = None], [int(x)] is
    [None], and the whole program is rejected.  (Before this free-identifier tightening such a program was
    WRONGLY accepted — emitting Go that does not compile.) *)
Definition unsupported_conv_freevar_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int" eq_refl)) [EId (mkIdent "x" eq_refl)]])].
Example conv_freevar_arg_unsupported : supported_program unsupported_conv_freevar_arg = false.
Proof. reflexivity. Qed.
Fail Example conv_freevar_arg_supported : SupportedProgram unsupported_conv_freevar_arg := eq_refl.

(** POSITIVE (Phase 4, [EConv]) — a slice/chan type-FORM conversion of the predeclared [nil] is a VALUE, used
    via [_ = ...]: `func main(){ _ = []int(nil) }` is supported ([[]int(nil)] is an [EConv] of [PtNil], a valid
    [svalue] of category [PtAgg]).  [nil] is the ONLY admitted conversion operand: with a FREE ident the
    conversion is REJECTED (`_ = []int(x)`, below).  As an AGGREGATE it is NOT a [println] arg (that printing is
    implementation-defined — see [printable_arg_ok]): `func main(){ println([]int(nil)) }` is rejected.  A bare
    [EConv] statement `func main(){ []int(nil) }` is also rejected ([expr_stmt_ok] admits only [ECall (EId _) _]). *)
Definition supported_conv_composite_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))].
Example conv_composite_arg_supported : SupportedProgram supported_conv_composite_arg.
Proof. reflexivity. Qed.
(** TIGHTENING (external review 2026-06-29) — the SAME conversion of a FREE identifier `func main(){ _ = []int(x) }`
    is NOT supported ([ptype (EId "x") = None], so [[]int(x)] is [None]); only [nil] is an admitted operand. *)
Definition unsupported_conv_composite_freevar : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl)))].
Example conv_composite_freevar_unsupported : supported_program unsupported_conv_composite_freevar = false.
Proof. reflexivity. Qed.
Fail Example conv_composite_freevar_supported : SupportedProgram unsupported_conv_composite_freevar := eq_refl.
(** A bare [EConv] statement `func main(){ []int(nil) }` is rejected (not a call) even though the SAME value is
    a valid blank-assign RHS above — isolating the value-vs-statement shape rule. *)
Definition unsupported_conv_composite_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))].
Example conv_composite_stmt_unsupported : supported_program unsupported_conv_composite_stmt = false.
Proof. reflexivity. Qed.
Fail Example conv_composite_stmt_supported : SupportedProgram unsupported_conv_composite_stmt := eq_refl.
(** [println] of a slice/aggregate is NOT supported (implementation-defined printing) — pinned on the valid
    [[]int(nil)] aggregate, so the ONLY reason for rejection is non-printability. *)
Definition unsupported_println_aggregate : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl))])].
Example println_aggregate_unsupported : supported_program unsupported_println_aggregate = false.
Proof. reflexivity. Qed.

(** POSITIVE (Phase 4, [ESliceLit]) — a slice composite literal is a VALUE, used via [_ = ...]: `func main(){
    _ = []int{1} }` is supported ([[]int{1}]'s element [1] is an [svalue]).  A bare [ESliceLit] statement
    `func main(){ []int{1} }` is rejected, and `func main(){ println([]int{1}) }` is rejected (a slice is not
    [printable_arg_ok]). *)
Definition supported_slicelit_arg : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign (ESliceLit GTInt [EInt 1])].
Example slicelit_arg_supported : SupportedProgram supported_slicelit_arg.
Proof. reflexivity. Qed.
Definition unsupported_slicelit_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ESliceLit GTInt [EInt 1])].
Example slicelit_stmt_unsupported : supported_program unsupported_slicelit_stmt = false.
Proof. reflexivity. Qed.
Fail Example slicelit_stmt_supported : SupportedProgram unsupported_slicelit_stmt := eq_refl.
Definition unsupported_println_slicelit : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [ESliceLit GTInt [EInt 1]])].
Example println_slicelit_unsupported : supported_program unsupported_println_slicelit = false.
Proof. reflexivity. Qed.

(** QUARANTINE ([EMapLit]): a map composite literal is REPRESENTABLE and round-trips in GoPrint, but is NOT in
    the supported subset ([svalue (EMapLit _ _ _) = false]) — Go requires the key TYPE be COMPARABLE
    (slice/map/func keys forbidden) AND keys/values be assignable to K/V, NEITHER of which is soundly structural
    here, so admitting it would certify invalid Go.  So NONE of these is supported:
    a comparable-key `_ = map[int]int{1: 2}`, the NON-comparable-key `_ = map[[]int]int{[]int{1}: 2}` (invalid
    Go), a map CONVERSION `_ = map[int]int(x)` (same key-type concern), the bare `map[int]int{1: 2}` statement,
    and `println(map[int]int{1: 2})` (aggregate).  Re-admit once GoSem seals a comparable-key builder +
    key/value assignability evidence — a clean AST/gate separation, NOT a deferred-to-later admission. *)
Definition unsupported_maplit_blank : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign (EMapLit GTInt GTInt [(EInt 1, EInt 2)])].
Example maplit_blank_unsupported : supported_program unsupported_maplit_blank = false.
Proof. reflexivity. Qed.
Fail Example maplit_blank_supported : SupportedProgram unsupported_maplit_blank := eq_refl.
Definition unsupported_maplit_noncomparable : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)])].
Example maplit_noncomparable_unsupported : supported_program unsupported_maplit_noncomparable = false.
Proof. reflexivity. Qed.
Definition unsupported_mapconv_blank : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EConv (CTMap GTInt GTInt) (EId (mkIdent "x" eq_refl)))].
Example mapconv_blank_unsupported : supported_program unsupported_mapconv_blank = false.
Proof. reflexivity. Qed.
Definition unsupported_maplit_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EMapLit GTInt GTInt [(EInt 1, EInt 2)])].
Example maplit_stmt_unsupported : supported_program unsupported_maplit_stmt = false.
Proof. reflexivity. Qed.
Fail Example maplit_stmt_supported : SupportedProgram unsupported_maplit_stmt := eq_refl.
Definition unsupported_println_maplit : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])].
Example println_maplit_unsupported : supported_program unsupported_println_maplit = false.
Proof. reflexivity. Qed.

(** REGRESSION — the [ptype] type-checker rejects CLOSED type-errors that a shape-only [printable_arg_ok] used
    to leak.  Each of these is a closed program Go rejects on the structure, so the gate must too — all
    [supported_program = false]: [println(len(1))] (an int is not len-able), [println(bool(1))] (int is not
    convertible to bool), [println(1 && 2)] (`&&` needs bool operands), [println(!1)] (`!` needs a bool), and
    [println(int([]int{1}))] (a slice is not convertible to int). *)
Definition pl_arg (a : GExpr) : Program :=   (* `func main(){ println(<a>) }` *)
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [a])].
Example bad_println_len1 :
  supported_program (pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EInt 1])) = false.
Proof. reflexivity. Qed.
Example bad_println_bool1 :
  supported_program (pl_arg (ECall (EId (mkIdent "bool" eq_refl)) [EInt 1])) = false.
Proof. reflexivity. Qed.
Example bad_println_land :
  supported_program (pl_arg (EBn BLAnd (EInt 1) (EInt 2))) = false.
Proof. reflexivity. Qed.
Example bad_println_not1 :
  supported_program (pl_arg (EUn UNot (EInt 1))) = false.
Proof. reflexivity. Qed.
Example bad_println_int_slice :
  supported_program (pl_arg (ECall (EId (mkIdent "int" eq_refl)) [ESliceLit GTInt [EInt 1]])) = false.
Proof. reflexivity. Qed.

(** ============================================================================================
    REGRESSIONS (Codex stop-review, 2026-06-29) — the REFINED [ptype] rejects CLOSED-invalid Go a fat
    [PtNum] / single-comparison / shared-len-cap / shape-only-aggregate-conv gate used to certify.  Each is a
    closed program Go's type checker rejects, so the gate must too ([supported_program = false]).
    ============================================================================================ *)
Definition gs_blank (a : GExpr) : Program :=   (* `func main(){ _ = <a> }` — value position via a blank assign *)
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign a].
Definition gs_f64 (a : GExpr) : GExpr := ECall (EId (mkIdent "float64" eq_refl)) [a].
Definition gs_i64 (a : GExpr) : GExpr := ECall (EId (mkIdent "int64" eq_refl)) [a].
Definition gs_i32 (a : GExpr) : GExpr := ECall (EId (mkIdent "int32" eq_refl)) [a].
Definition gs_str (a : GExpr) : GExpr := ECall (EId (mkIdent "string" eq_refl)) [a].
Definition gs_x : GExpr := EId (mkIdent "x" eq_refl).

(** FINDING 1 — numeric category split.  Float modulo / float shift+bitwise (a FLOAT operand is rejected for
    [%] / [<<] / [&]); constant overflow at a fixed-width conversion ([uint8(300)], [int8(128)]) and at a
    slice-literal element ([[]uint8{300}]); mixed fixed-width arithmetic ([int64(3) + int32(2)]). *)
Example bad_float_mod : supported_program (pl_arg (EBn BRem (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))) = false.
Proof. reflexivity. Qed.
Example bad_float_shl : supported_program (pl_arg (EBn BShl (gs_f64 (EInt 1)) (EInt 2))) = false.
Proof. reflexivity. Qed.
Example bad_float_and : supported_program (pl_arg (EBn BAnd (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))) = false.
Proof. reflexivity. Qed.
Example bad_float_compl : supported_program (pl_arg (EUn UXor (gs_f64 (EInt 1)))) = false.
Proof. reflexivity. Qed.
Example bad_uint8_overflow : supported_program (pl_arg (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 300])) = false.
Proof. reflexivity. Qed.
Example bad_int8_overflow : supported_program (pl_arg (ECall (EId (mkIdent "int8" eq_refl)) [EInt 128])) = false.
Proof. reflexivity. Qed.
Example bad_uint8_slicelit : supported_program (gs_blank (ESliceLit GTU8 [EInt 300])) = false.
Proof. reflexivity. Qed.
Example bad_mixed_width : supported_program (pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i32 (EInt 2)))) = false.
Proof. reflexivity. Qed.
Example bad_int_slicelit_typed : supported_program (gs_blank (ESliceLit GTInt [gs_i64 (EInt 1)])) = false.
Proof. reflexivity. Qed.
Fail Example bad_uint8_overflow_forge : SupportedProgram (pl_arg (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 300])) := eq_refl.

(** FINDING 1 (adversarial) — CONSTANT division / modulo / shift by ZERO is a compile error in Go, INCLUDING
    a zero FOLDED from a constant subexpression ([1 / (1 - 1)]).  [ptype] folds constants, so it catches all.
    A NEGATIVE constant shift count is rejected (shown over a VALID constant left operand, so the rejection is
    attributable to the count, not the operand). *)
Example bad_div_zero : supported_program (pl_arg (EBn BDiv (EInt 1) (EInt 0))) = false.
Proof. reflexivity. Qed.
Example bad_div_zero_folded : supported_program (pl_arg (EBn BDiv (EInt 1) (EBn BSub (EInt 1) (EInt 1)))) = false.
Proof. reflexivity. Qed.
Example bad_mod_zero : supported_program (pl_arg (EBn BRem (EInt 1) (EInt 0))) = false.
Proof. reflexivity. Qed.
Example bad_neg_shift : supported_program (pl_arg (EBn BShl (EInt 1) (EInt (-1)))) = false.
Proof. reflexivity. Qed.

(** FINDING 2 — comparison split by operator.  Equality needs COMPARABLE operands (slice equality rejected;
    cross-kind [1 == (2==2)] rejected); ordering needs ORDERED operands (bool ordering [(1==1) < (2==2)] and
    slice ordering rejected). *)
Example bad_slice_eq :
  supported_program (pl_arg (EBn BEq (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))) = false.
Proof. reflexivity. Qed.
Example bad_slice_ord :
  supported_program (pl_arg (EBn BLt (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))) = false.
Proof. reflexivity. Qed.
Example bad_bool_ord :
  supported_program (pl_arg (EBn BLt (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)))) = false.
Proof. reflexivity. Qed.
Example bad_eq_crosskind :
  supported_program (pl_arg (EBn BEq (EInt 1) (EBn BEq (EInt 2) (EInt 2)))) = false.
Proof. reflexivity. Qed.
Fail Example bad_bool_ord_forge :
  SupportedProgram (pl_arg (EBn BLt (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)))) := eq_refl.

(** FINDING 3 — [len]/[cap] separated.  [cap] of a STRING is rejected (the rune-const [cap(string(65))] and the
    string-literal [cap("hi")]); [len] of a string stays OK ([len("hi")]). *)
Example bad_cap_string_lit : supported_program (gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [gs_str (EInt 65)])) = false.
Proof. reflexivity. Qed.
Example bad_cap_string : supported_program (gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EStr "hi"])) = false.
Proof. reflexivity. Qed.
Example ok_len_string : SupportedProgram (pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"])).
Proof. reflexivity. Qed.

(** FINDING 4 — aggregate conversion soundness.  A slice->chan conversion of a KNOWN slice ([chan int([]int{1})])
    and a mismatched slice conversion of a KNOWN slice ([[]int([]string{})]) are rejected; only the predeclared
    [nil] operand ([[]int(nil)]) is admitted (pinned below by [conv_composite_arg_supported]). *)
Example bad_chan_of_slice : supported_program (gs_blank (EConv (CTChan GTInt) (ESliceLit GTInt [EInt 1]))) = false.
Proof. reflexivity. Qed.
Example bad_slice_conv_mismatch : supported_program (gs_blank (EConv (CTSlice GTInt) (ESliceLit GTString []))) = false.
Proof. reflexivity. Qed.
Fail Example bad_chan_of_slice_forge : SupportedProgram (gs_blank (EConv (CTChan GTInt) (ESliceLit GTInt [EInt 1]))) := eq_refl.

(** POSITIVES — the refined gate still admits the well-typed forms (a smaller-but-SOUND subset, not empty):
    in-range conversions, FOLDED constant arithmetic/shift, an untyped const into a float element, same-width
    typed arithmetic. *)
Example ok_int8_inrange : SupportedProgram (pl_arg (ECall (EId (mkIdent "int8" eq_refl)) [EInt 127])).
Proof. reflexivity. Qed.
Example ok_const_mod : SupportedProgram (pl_arg (EBn BRem (EInt 5) (EInt 2))).
Proof. reflexivity. Qed.
Example ok_const_shift : SupportedProgram (pl_arg (EBn BShl (EInt 1) (EInt 4))).
Proof. reflexivity. Qed.
Example ok_float_slicelit : SupportedProgram (gs_blank (ESliceLit GTFloat64 [EInt 1])).
Proof. reflexivity. Qed.
Example ok_same_width_add : SupportedProgram (pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i64 (EInt 2)))).
Proof. reflexivity. Qed.

(** ============================================================================================
    REGRESSIONS (Codex stop-review, 2026-06-29 #2) — CONSTANTNESS now SURVIVES conversions/binops, so the
    TRANSITIVE constant rules (a conversion of a constant is itself a typed CONSTANT) are enforced.  The prior
    [conv_to_scalar] ERASED the value ([PtIntConst z] -> [PtInt t]), so these CLOSED compile errors sailed
    through.  Each is a closed program Go's type checker rejects ([supported_program = false]).
    ============================================================================================ *)
Definition gs_int (a : GExpr) : GExpr := ECall (EId (mkIdent "int" eq_refl)) [a].
Definition gs_u8  (a : GExpr) : GExpr := ECall (EId (mkIdent "uint8" eq_refl)) [a].
Definition gs_i8  (a : GExpr) : GExpr := ECall (EId (mkIdent "int8" eq_refl)) [a].

(** THE 5 NAMED — a typed-constant divisor zero ([int(0)]), modulo zero, a typed-constant negative shift count
    ([int(-1)]), and an out-of-range CONSTANT conversion that hops through int / float ([uint8(int(300))],
    [uint8(float64(300))]).  All [false]; two locked by a [Fail … := eq_refl] forge-attempt. *)
Example bad_div_int0   : supported_program (pl_arg (EBn BDiv (EInt 1) (gs_int (EInt 0)))) = false.
Proof. reflexivity. Qed.
Example bad_mod_int0   : supported_program (pl_arg (EBn BRem (EInt 1) (gs_int (EInt 0)))) = false.
Proof. reflexivity. Qed.
Example bad_shl_intneg : supported_program (pl_arg (EBn BShl (EInt 1) (gs_int (EInt (-1))))) = false.
Proof. reflexivity. Qed.
Example bad_uint8_of_int300 : supported_program (pl_arg (gs_u8 (gs_int (EInt 300)))) = false.
Proof. reflexivity. Qed.
Example bad_uint8_of_float300 : supported_program (pl_arg (gs_u8 (gs_f64 (EInt 300)))) = false.
Proof. reflexivity. Qed.
Fail Example bad_div_int0_forge : SupportedProgram (pl_arg (EBn BDiv (EInt 1) (gs_int (EInt 0)))) := eq_refl.
Fail Example bad_uint8_of_int300_forge : SupportedProgram (pl_arg (gs_u8 (gs_int (EInt 300)))) := eq_refl.

(** ADVERSARIAL transitivity / overflow / boundary — a typed-constant ARITHMETIC RESULT that overflows its
    type ([int8(100)+int8(100)] = 200), a DOUBLE conversion ([uint8(int(int(300)))]), a constant zero divisor
    FOLDED from typed-const subexpressions ([1/(int(1)-int(1))]), an UNTYPED constant whose default-[int] value
    OVERFLOWS the 32-bit boundary ([println(<2^40>)]), and a typed-constant slice element of the WRONG type /
    out of range ([[]uint8{int(300)}]).  All [false]. *)
Example bad_int8_add_overflow : supported_program (pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 100)))) = false.
Proof. reflexivity. Qed.
Example bad_uint8_of_int_int300 : supported_program (pl_arg (gs_u8 (gs_int (gs_int (EInt 300))))) = false.
Proof. reflexivity. Qed.
Example bad_div_folded_typed_zero :
  supported_program (pl_arg (EBn BDiv (EInt 1) (EBn BSub (gs_int (EInt 1)) (gs_int (EInt 1))))) = false.
Proof. reflexivity. Qed.
Example bad_println_default_int_overflow :
  supported_program (pl_arg (EInt 1099511627776)) = false.   (* 2^40, does not fit 32-bit int *)
Proof. reflexivity. Qed.
Example bad_blank_default_int_overflow :
  supported_program (gs_blank (EInt 1099511627776)) = false.
Proof. reflexivity. Qed.
Example bad_uint8_slicelit_typed : supported_program (gs_blank (ESliceLit GTU8 [gs_int (EInt 300)])) = false.
Proof. reflexivity. Qed.

(** POSITIVES — the constant-aware gate still admits the SOUND forms, and tracks float→int constant conversions
    EXACTLY: an in-range constant hopping through float is ACCEPTED ([uint8(float64(255))] — value 255 is in
    [uint8] range, so this is VALID Go and we certify it), folded typed-const arithmetic in range
    ([int8(100)+int8(20)] = 120), and a value at the 32-bit default-[int] boundary ([println(2147483647)]). *)
Example ok_uint8_of_float255 : SupportedProgram (pl_arg (gs_u8 (gs_f64 (EInt 255)))).
Proof. reflexivity. Qed.
Example ok_int8_add_inrange : SupportedProgram (pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 20)))).
Proof. reflexivity. Qed.
Example ok_println_int_max : SupportedProgram (pl_arg (EInt 2147483647)).
Proof. reflexivity. Qed.

(** ============================================================================================
    REGRESSION — FLOAT-CONSTANT ROUNDING + PLATFORM-WIDTH COMPLEMENT (the constant rep must not LIE).
    (1) A float CONSTANT [float64(n)] is tracked as exact ONLY within the CONTIGUOUS exact interval [|n| <= 2^53]
    (float32: 2^24) — a CONSERVATIVE SUFFICIENT test, NOT the full set of exactly-representable integers (e.g.
    [2^60] is an exact [float64] but lies outside the interval).  An OUTSIDE-interval integer MAY be exact OR
    rounded; the gate does not model that sparse relation, so it conservatively REJECTS the const->float
    conversion for ANY outside-interval constant.  One rejected case is a ROUNDED overflow,
    [int64(float64(9223372036854775807))]: the float64 rounds maxint64 UP to 2^63, which overflows [int64]
    (likewise [int32(float32(maxint32))]).  (2) A typed FLOAT-constant ZERO
    [float64(0)] is a constant-zero divisor (Go rejects constant float division by zero), so [_ = x / float64(0)]
    is REJECTED (the divisor is a constant-zero — and the free dividend [x] is itself rejected in the
    no-declaration model).  (3) [^uint(0)] = 2^w-1 is PLATFORM-WIDTH-dependent, so folding it
    to one width is unsound: [uint32(^uint(0))] is in range on 32-bit Go but NOT 64-bit — the gate REJECTS
    platform-`uint` complement.  All [false].  PRESERVED positives: [uint8(float64(255))] (255 is EXACT and in
    range) and the FIXED-WIDTH [uint8(^uint8(0))] (= 255, width is fixed → exact). *)
Example bad_i64_of_f64max :
  supported_program (pl_arg (gs_i64 (gs_f64 (EInt 9223372036854775807)))) = false.
Proof. reflexivity. Qed.
Example bad_i32_of_f32max :
  supported_program (pl_arg (gs_i32 (ECall (EId (mkIdent "float32" eq_refl)) [EInt 2147483647]))) = false.
Proof. reflexivity. Qed.
Example bad_div_float_zero :
  supported_program (gs_blank (EBn BDiv (EId (mkIdent "x" eq_refl)) (gs_f64 (EInt 0)))) = false.
Proof. reflexivity. Qed.
Example bad_uint32_of_compl_uint :
  supported_program (pl_arg (ECall (EId (mkIdent "uint32" eq_refl))
                                   [EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [EInt 0])])) = false.
Proof. reflexivity. Qed.
Fail Example bad_i64_of_f64max_forge :
  SupportedProgram (pl_arg (gs_i64 (gs_f64 (EInt 9223372036854775807)))) := eq_refl.
Fail Example bad_uint32_of_compl_uint_forge :
  SupportedProgram (pl_arg (ECall (EId (mkIdent "uint32" eq_refl))
                                  [EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [EInt 0])])) := eq_refl.
Example ok_uint8_of_float255_exact : SupportedProgram (pl_arg (gs_u8 (gs_f64 (EInt 255)))).
Proof. reflexivity. Qed.
Example ok_uint8_compl_uint8 :
  SupportedProgram (pl_arg (gs_u8 (EUn UXor (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 0])))).
Proof. reflexivity. Qed.

(** HELPER-LEVEL regression — the unsound platform-[uint] complement is sealed INSIDE [complement_const]
    (returns [None]), so it cannot be produced regardless of caller; fixed-width unsigned ([uint8]) and signed
    ([int]) still fold exactly. *)
Example complement_const_uint_none : complement_const GTUint 0 = None.
Proof. reflexivity. Qed.
Example complement_const_u8_exact : complement_const GTU8 0 = Some 255%Z.
Proof. reflexivity. Qed.
Example complement_const_int_signed : complement_const GTInt 0 = Some (-1)%Z.
Proof. reflexivity. Qed.

(** REGRESSION (external review 2026-06-28, follow-up⁴) — a VOID call used as a VALUE, `func main(){
    println(println(1)) }`, is invalid Go (the inner [println] returns NOTHING, so it cannot be an argument:
    "println(1) (no value) used as value").  [svalue] admits an application only as a CONVERSION ([EId] of a
    builtin type, one arg) — [println] is not a type — so the inner [println(1)] is NOT a valid value and the
    whole program is NOT supported.  (Pins that value position is conversion-only, not any call.) *)
Definition unsupported_void_call_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "println" eq_refl)) [EInt 1]])].
Example void_call_arg_unsupported : supported_program unsupported_void_call_arg = false.
Proof. reflexivity. Qed.
Fail Example void_call_arg_supported : SupportedProgram unsupported_void_call_arg := eq_refl.

(** REGRESSION (external review 2026-06-28, follow-up⁵) — CONVERSION ARITY: `func main(){ println(int(1, 2)) }`
    is invalid Go ("too many arguments to conversion to int").  [svalue]'s conversion case matches EXACTLY one
    arg ([a :: nil]), so the 2-arg [int(1, 2)] is NOT a valid value and the program is NOT supported.  Pins the
    arity bound that distinguishes this from the supported 1-arg [println(int(x))] above (and likewise rejects
    the 0-arg [int()]). *)
Definition unsupported_conv_arity : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int" eq_refl)) [EInt 1; EInt 2]])].
Example conv_arity_unsupported : supported_program unsupported_conv_arity = false.
Proof. reflexivity. Qed.
Fail Example conv_arity_supported : SupportedProgram unsupported_conv_arity := eq_refl.

(** GROWTH (Phase 4) — [panic] joins the supported statement builtins.  [panic] takes EXACTLY ONE arg of ANY
    type, so `func main(){ panic(1) }` is a valid statement and IS supported; the arity violations [panic()]
    and [panic(1, 2)] are NOT (this is how a new builtin re-enters: with its arity checked).  Pins all three. *)
Definition supported_panic : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1])].
Example panic_supported : SupportedProgram supported_panic.
Proof. reflexivity. Qed.
Definition unsupported_panic_nullary : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) nil)].
Example panic_nullary_unsupported : supported_program unsupported_panic_nullary = false.
Proof. reflexivity. Qed.
Fail Example panic_nullary_supported : SupportedProgram unsupported_panic_nullary := eq_refl.
Definition unsupported_panic_binary : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1; EInt 2])].
Example panic_binary_unsupported : supported_program unsupported_panic_binary = false.
Proof. reflexivity. Qed.

(** REGRESSION (Phase 4, [GsReturnVal]) — a VALUE return in the void [main], `func main(){ return 1 }`, is
    invalid Go ("too many return values"), so [stmt_ok] rejects [GsReturnVal] and the program is NOT supported
    (whereas the bare `func main(){ return }` IS — pinned by [supported_bare_return]).  This demonstrates the
    AST/gate separation: the AST CAN represent `return e`, the printer round-trips it, but the supportedness
    gate refuses it because the only function emitted is void.  Becomes supported once non-void functions land. *)
Definition unsupported_return_value : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsReturnVal (EInt 1)].
Example return_value_unsupported : supported_program unsupported_return_value = false.
Proof. reflexivity. Qed.
Fail Example return_value_supported : SupportedProgram unsupported_return_value := eq_refl.
Definition supported_bare_return : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsReturn].
Example bare_return_supported : SupportedProgram supported_bare_return.
Proof. reflexivity. Qed.

(** GROWTH (Phase 4, [GsBlankAssign]) — the blank assignment `func main(){ _ = 1 }` is a valid statement
    (discards the value [1]) and IS supported — the FIRST supported statement that is neither a call nor a
    return.  Its operand must PRODUCE a value ([svalue]): `func main(){ _ = println(1) }` is invalid Go
    ("println(1) (no value) used as value"), and [svalue (println 1) = false] (only a CONVERSION is a value
    application), so it is NOT supported.  Pins both. *)
Definition supported_blank_assign : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign (EInt 1)].
Example blank_assign_supported : SupportedProgram supported_blank_assign.
Proof. reflexivity. Qed.
Definition unsupported_blank_void : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])].
Example blank_void_unsupported : supported_program unsupported_blank_void = false.
Proof. reflexivity. Qed.
Fail Example blank_void_supported : SupportedProgram unsupported_blank_void := eq_refl.

(** GROWTH (Phase 4, value-returning builtins [len]/[cap]) — the Go-spec value-vs-statement asymmetry.  A
    value-returning builtin is fine in VALUE position: `func main(){ println(len([]int{1})) }` is supported
    ([len([]int{1})] is an [svalue]); and `func main(){ _ = cap([]int{1}) }` likewise.  But it is FORBIDDEN in
    STATEMENT position ("len … not permitted in statement context"): `func main(){ len([]int{1}) }` is NOT
    supported ([stmt_call_ok] excludes [len]).  Arity is pinned: `func main(){ println(len([]int{1}, []int{1})) }`
    is NOT supported (len takes one arg, so the 2-arg form is not an [svalue]).  Pins all four.  (The operand is
    an aggregate, not a free ident, so each pin isolates its real reason — the free-ident [len(x)]/[cap(x)] are
    rejected separately below.) *)
Definition supported_len_value : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]])].
Example len_value_supported : SupportedProgram supported_len_value.
Proof. reflexivity. Qed.
Definition supported_cap_blank : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (ECall (EId (mkIdent "cap" eq_refl)) [ESliceLit GTInt [EInt 1]])].
Example cap_blank_supported : SupportedProgram supported_cap_blank.
Proof. reflexivity. Qed.
Definition unsupported_len_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])].
Example len_stmt_unsupported : supported_program unsupported_len_stmt = false.
Proof. reflexivity. Qed.
Fail Example len_stmt_supported : SupportedProgram unsupported_len_stmt := eq_refl.
Definition unsupported_len_arity : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl))
                                      [ESliceLit GTInt [EInt 1]; ESliceLit GTInt [EInt 1]]])].
Example len_arity_unsupported : supported_program unsupported_len_arity = false.
Proof. reflexivity. Qed.

(** ============================================================================================
    TIGHTENING (external review 2026-06-29) — FREE-IDENTIFIER REJECTION.  The no-declaration Program model has
    no variable bindings, so a FREE identifier is UNDEFINED and the emitted Go would not compile.  [ptype
    (EId i)] now returns a category ONLY for the predeclared value-ident [nil]; every other identifier is
    [None].  So each of these — a bare `_ = x`, a [len]/[cap] of a free ident, a [panic] of a free ident — is
    NOT supported, where the pre-tightening gate WRONGLY certified them.  (The supported aggregate forms above
    pin that [len]/[cap] themselves stay admitted — only the FREE OPERAND is the defect.)  All [false]; the
    forge-attempts lock them. *)
Definition unsupported_free_blank : Program :=   (* `func main(){ _ = x }` — use of an undefined identifier *)
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign (EId (mkIdent "x" eq_refl))].
Example free_blank_unsupported : supported_program unsupported_free_blank = false.
Proof. reflexivity. Qed.
Fail Example free_blank_supported : SupportedProgram unsupported_free_blank := eq_refl.
Definition unsupported_free_len : Program :=   (* `func main(){ println(len(x)) }` *)
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl)) [EId (mkIdent "x" eq_refl)]])].
Example free_len_unsupported : supported_program unsupported_free_len = false.
Proof. reflexivity. Qed.
Fail Example free_len_supported : SupportedProgram unsupported_free_len := eq_refl.
Definition unsupported_free_cap : Program :=   (* `func main(){ _ = cap(x) }` *)
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (ECall (EId (mkIdent "cap" eq_refl)) [EId (mkIdent "x" eq_refl)])].
Example free_cap_unsupported : supported_program unsupported_free_cap = false.
Proof. reflexivity. Qed.
Fail Example free_cap_supported : SupportedProgram unsupported_free_cap := eq_refl.
Definition unsupported_free_panic : Program :=   (* `func main(){ panic(x) }` *)
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EId (mkIdent "x" eq_refl)])].
Example free_panic_unsupported : supported_program unsupported_free_panic = false.
Proof. reflexivity. Qed.
Fail Example free_panic_supported : SupportedProgram unsupported_free_panic := eq_refl.

(** GROWTH (Phase 4, [EStr]) — the string-literal expression joins the supported subset.  [ptype (EStr _) =
    Some PtStr] (the printable SCALAR string category), so a string literal is a valid [svalue] AND a valid
    [printable_arg_ok] argument: `func main(){ println("hi") }` IS supported (the FIRST [println] of a literal
    payload — strings previously existed only as a TYPE and as conversions), and `func main(){ _ = "x" }` IS
    supported (a string is a value).  A BARE string statement `func main(){ "x" }` is NOT supported
    ([expr_stmt_ok] admits only a call [ECall (EId _) _], and a string literal is not call-shaped), pinning
    the value-vs-statement asymmetry.  An empty string and one needing escapes round-trip too (GoPrint). *)
Definition supported_println_str : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EStr "hi"])].
Example println_str_supported : SupportedProgram supported_println_str.
Proof. reflexivity. Qed.
Definition supported_blank_str : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign (EStr "x")].
Example blank_str_supported : SupportedProgram supported_blank_str.
Proof. reflexivity. Qed.
(** the printable / value classification of a string literal, pinned directly. *)
Example str_printable : printable_arg_ok (EStr "hi") = true.
Proof. reflexivity. Qed.
Example str_svalue : svalue (EStr "x") = true.
Proof. reflexivity. Qed.
(** a BARE string-literal expression statement is NOT a call, so NOT supported. *)
Definition unsupported_bare_str : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EStr "x")].
Example bare_str_unsupported : supported_program unsupported_bare_str = false.
Proof. reflexivity. Qed.
Fail Example bare_str_supported : SupportedProgram unsupported_bare_str := eq_refl.
(** ANTI-REGRESSION — a non-printable AGGREGATE arg to [println] is STILL rejected ([[]int{1}] is not a
    printable scalar), confirming the [EStr] addition did not loosen [printable_arg_ok] for non-scalars. *)
Example println_slicelit_still_unsupported :
  supported_program (pl_arg (ESliceLit GTInt [EInt 1])) = false.
Proof. reflexivity. Qed.

(** ===================================================================================================
    ===== SEMANTIC: BehaviorSafe over GoSem (future) =====
    =================================================================================================== *)

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions value_stmt_unsupported.
