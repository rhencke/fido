(** GoTypes.v — the SHARED constant-aware type-category checker (AST-first spine; see ARCHITECTURE.md).
    A LOWER module (imports ONLY GoAst, below GoSafe): it owns [ptype] ([GExpr -> option PTy], the structural
    constant-aware TYPE-CATEGORY assignment), its numeric/conversion combinators, and the value-position wrapper
    [svalue] — so the layers above share ONE type authority (GoSafe's [SupportedProgram] rejects a free ident /
    closed type-error because [ptype] does — the pinning regressions live in GoSafe; GoSem slice-1's blank-assign
    gates on [svalue]).  NO theorems (only [Definition]s / one [Inductive]) ⇒ NO axioms. *)
From Fido Require Import GoAst.   (* GoAst supplies the syntax ([GExpr]/[GoTy]/[BinOp]/…) AND [classify]
                                     (the keyword -> [GoTy] map for scalar conversions).  DELIBERATELY the
                                     ONLY Fido import — GoTypes is the bottom of the type-category layer. *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ===================================================================================================
    ===== TYPE-CATEGORY: ptype classifier (PTy + numeric/conversion combinators) =====
    =================================================================================================== *)

(** ★TOP INVARIANT — [ptype] is a CONSERVATIVE SUPPORTED-SUBSET classifier, NOT Go's
    typechecker: no [ptype]-vs-Go theorem (that is GoSem's job); it REJECTS anything not
    clearly supported, over-rejecting much valid Go.  Value-aware ONLY for the NUMERIC
    constant categories ([PtIntConst]/[PtTIntConst]/[PtFloatConst]): a numeric constant
    carries its VALUE (a [Z]; floats an exact DYADIC [m * 2^e]) so overflow /
    div-or-shift-by-zero are decided from the folded value, transitively through
    all-constant numeric conversions/binops; a typed const also carries its [GoTy]
    (mixed-width + out-of-range rejected); a runtime numeric carries only its [GoTy].
    ANTI-REGRESSION: an all-constant numeric op preserves/folds the value or is REJECTED —
    never silently a runtime category; a MIXED const/runtime op is runtime BY CONSTRUCTION.
    ⚠ STRING/BOOL constants are NOT value-carrying: a form needing the folded value
    fail-CLOSES ([len("a"+"b")] is valid Go that Fido rejects — pinned in
    [GoSafe.valid_unsupported_programs]; [bad_programs] holds INVALID Go).  A FREE
    identifier is REJECTED (no-declaration model); [nil] ([PtNil]) is admitted only inside
    a slice/chan conversion.  A new [ptype] rule lands ONLY if it rejects a real
    accepted-bad closed program or admits an intentionally supported demo; relied-on
    closed-invalid classes are PINNED in [GoSafe.bad_programs] (curated fixtures, not an
    exhaustive rejection theorem). *)
(** ---- DYADIC float-constant values ---- a typed float CONSTANT carries the EXACT value [m * 2^e]
    ([m e : Z], NORMALIZED: [m = 0 -> e = 0], else [m] odd) — the same shape as the model's
    [S754_finite s m e] (spec_float IS ±m·2^e), so GoSem's [box_float] renders it without translation.
    Posture: EXACT-OR-REJECT — [+]/[-]/[*] are always exact on dyadics; [/] is exact iff the (odd,
    normalized) divisor mantissa divides the dividend's, else [None]; a result not exactly representable
    at the TYPE's width ([float_dyadic_repr]) is REJECTED.  Go rounds each typed-const op to the type —
    when the exact result IS representable, IEEE correct rounding returns it unchanged, so the fold
    agrees with Go wherever it accepts (a rounding case like [float64(1)/float64(3)] is valid Go that
    Fido REJECTS: quarantined incompleteness, never a wrong value). *)
Fixpoint pos_odd_split (p : positive) : positive * Z :=
  match p with
  | xO p' => let '(q, k) := pos_odd_split p' in (q, Z.succ k)
  | _ => (p, 0%Z)
  end.
Definition dy_norm (m e : Z) : Z * Z :=
  match m with
  | Z0 => (0%Z, 0%Z)
  | Zpos p => let '(q, k) := pos_odd_split p in (Zpos q, Z.add e k)
  | Zneg p => let '(q, k) := pos_odd_split p in (Zneg q, Z.add e k)
  end.
Definition dy_add (a b : Z * Z) : Z * Z :=
  let '(m1, e1) := a in let '(m2, e2) := b in
  if Z.leb e1 e2 then dy_norm (Z.add m1 (Z.shiftl m2 (Z.sub e2 e1))) e1
                 else dy_norm (Z.add (Z.shiftl m1 (Z.sub e1 e2)) m2) e2.
Definition dy_neg (a : Z * Z) : Z * Z := let '(m, e) := a in (Z.opp m, e).
Definition dy_sub (a b : Z * Z) : Z * Z := dy_add a (dy_neg b).
Definition dy_mul (a b : Z * Z) : Z * Z :=
  let '(m1, e1) := a in let '(m2, e2) := b in dy_norm (Z.mul m1 m2) (Z.add e1 e2).
(** Exact dyadic division — inputs NORMALIZED (so [m2] is odd when nonzero): the quotient is dyadic iff
    [m2 | m1]; the zero divisor never reaches here ([is_zero_const] guards [BDiv] upstream). *)
Definition dy_div (a b : Z * Z) : option (Z * Z) :=
  let '(m1, e1) := a in let '(m2, e2) := b in
  if Z.eqb m2 0 then None
  else if Z.eqb (Z.rem m1 m2) 0 then Some (dy_norm (Z.quot m1 m2) (Z.sub e1 e2))
  else None.
(** Align two dyadics to the smaller exponent (EXACT — only left-shifts): the aligned mantissa pair
    compares/relates exactly as the values do. *)
Definition dy_align (a b : Z * Z) : Z * Z :=
  let '(m1, e1) := a in let '(m2, e2) := b in
  if Z.leb e1 e2 then (m1, Z.shiftl m2 (Z.sub e2 e1)) else (Z.shiftl m1 (Z.sub e1 e2), m2).
(** EXACT representability of a NORMALIZED dyadic at float type [t] — a CONSERVATIVE window (mantissa
    within the type's precision, exponent inside the always-exact finite range: binary64 [|m| < 2^53],
    [-1074 <= e <= 971] so [|v| < 2^1024]; binary32 [|m| < 2^24], [-149 <= e <= 104]).  Under-acceptance
    is fail-loud-safe; everything accepted boxes to its EXACT canonical form. *)
Definition float_dyadic_repr (t : GoTy) (m e : Z) : bool :=
  match t with
  | GTFloat64 => andb (Z.ltb (Z.abs m) 9007199254740992)
                      (andb (Z.leb (-1074) e) (Z.leb e 971))
  | GTFloat32 => andb (Z.ltb (Z.abs m) 16777216)
                      (andb (Z.leb (-149) e) (Z.leb e 104))
  | _ => false
  end.

(** The SEALED dyadic payload — normalization is STRUCTURAL, not a comment: [DyConst]'s proof field
    witnesses the carried pair is in the IMAGE of [dy_norm] (the [builtins.GoFloat32]/[mkF32] pattern —
    an unnormalized payload like [(2, 0)] is UNCONSTRUCTABLE: no [m0 e0] normalizes to it, so the
    [dy_div]-misbehaving states are impossible, not discouraged).  EVERY construction must exhibit the
    image witness: [dy_make] supplies it definitionally (no theorem, so this file's Definitions-only
    policy holds); a direct [mkDy] must PROVE its pair is [dy_norm]'s output — unprovable for an
    unnormalized pair, so the invariant is mechanical, not conventional. *)
Record DyConst : Type := mkDy {
  dy_m : Z ; dy_e : Z ;
  dy_ok : exists m0 e0, (dy_m, dy_e) = dy_norm m0 e0
}.
Definition dy_make (m e : Z) : DyConst :=
  mkDy (fst (dy_norm m e)) (snd (dy_norm m e))
       (ex_intro _ m (ex_intro _ e
          (match dy_norm m e as q return (fst q, snd q) = q with (a, b) => eq_refl end))).


Inductive PTy : Type :=
  | PtIntConst   (z : Z)            (* an UNTYPED INTEGER CONSTANT — value known, type not yet fixed (adapts on use) *)
  | PtTIntConst  (t : GoTy) (z : Z) (* a TYPED INTEGER CONSTANT of int-type [t], value [z] (from converting a const to [t]) *)
  | PtFloatConst (t : GoTy) (d : DyConst) (* a TYPED FLOAT CONSTANT (t = GTFloat64/GTFloat32), EXACT dyadic value [dy_m d * 2^(dy_e d)] — the payload is SEALED normalized ([DyConst], below the CONST layer; fractional values carryable: [float64(3)/float64(2)] is [(3, -1)]) *)
  | PtRunInt     (t : GoTy)         (* a RUNTIME (non-constant) integer of type [t] (e.g. [int(x)], [len([]int{..})] — note [len] of a STRING LITERAL folds to [PtIntConst], NOT this; a non-literal string const (["a"+"b"], [string(65)]) is supported as [PtStr] but carries no value, so [len] of IT is rejected) *)
  | PtRunFloat   (t : GoTy)         (* a RUNTIME (non-constant) float of type [t] (e.g. [float64(x)]) *)
  | PtBool
  | PtStr
  | PtAgg    (* a slice/chan aggregate value: a valid VALUE, [len]/[cap]-able, but never numeric / order-comparable / printable *)
  | PtMap    (* a MAP aggregate value: a valid VALUE, [len]-able but NOT [cap]-able (Go forbids [cap] of a map), never numeric / comparable / printable — DISTINCT from [PtAgg] precisely so [cap] rejects it *)
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
    result CATEGORY preserves the NUMERIC constant's value (num_arith only sees numeric categories):
    - both UNTYPED int consts -> a new UNTYPED int const (ARBITRARY PRECISION — no overflow until used);
    - untyped const + TYPED int const -> a TYPED const, with the FOLDED RESULT representability-checked in the
      type (so [int8(100)+int8(100)] = 200 -> REJECT) — and likewise typed+typed of the SAME type (DIFFERENT
      types REJECT: mixed width [int64(3)+int32(2)]);
    - a const combined with a RUNTIME int -> a runtime int of that type (the const must be REPRESENTABLE in /
      of the SAME type as the runtime), value no longer tracked (there is a runtime operand, so no fold);
    - runtime + runtime int -> same type;  runtime FLOAT + runtime float (or + untyped int const repr-as-float,
      or + a same-typed float CONST, value dropped) -> runtime float of that type;
    - float CONST ∘ float CONST (same type) and float CONST ∘ untyped int const: the EXACT dyadic fold
      ([dy_fold_at] — [+ - *] always exact, [/] exact-or-reject, result repr-checked at the type);
    - any non-numeric operand (bool/str/agg/nil) -> REJECT.
    Callers gate the INT-ONLY ops ([% & | ^ &^] and the shifts) with [is_int_cat] FIRST (their [dfold] is
    [None], so a float const cannot fold through them); the [/]-zero check is done by the caller. *)
(** The dyadic result of a float-CONSTANT op, repr-gated at the operands' (equal) type — the ONE place a
    folded float const is (re)admitted, so the payload invariant (normalized + [float_dyadic_repr]) holds
    by construction.  [dfold = None] = an int-only op (shift/bitwise/[%]) — float consts REJECTED. *)
Definition dy_fold_at (t : GoTy) (dfold : option ((Z * Z) -> (Z * Z) -> option (Z * Z)))
                      (a b : Z * Z) : option PTy :=
  match dfold with
  | None => None
  | Some f => match f a b with
              | Some (m, e) =>
                  let d := dy_make m e in
                  if float_dyadic_repr t (dy_m d) (dy_e d) then Some (PtFloatConst t d) else None
              | None => None
              end
  end.
Definition num_arith (fold : Z -> Z -> Z) (dfold : option ((Z * Z) -> (Z * Z) -> option (Z * Z)))
                     (cl cr : PTy) : option PTy :=
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
  (* ---- FLOAT CONSTANTS (dyadic, exact-or-reject; [dfold] carries the op) ---- *)
  (* float const + float const: SAME type, dyadic fold, repr-check the result *)
  | PtFloatConst t1 d1, PtFloatConst t2 d2 =>
      if numty_eqb t1 t2 then dy_fold_at t1 dfold (dy_m d1, dy_e d1) (dy_m d2, dy_e d2) else None
  (* float const + untyped int const (either side — operand ORDER preserved for [-]/[/]) *)
  | PtFloatConst t d, PtIntConst z =>
      if int_in_float_exact_interval t z then dy_fold_at t dfold (dy_m d, dy_e d) (dy_norm z 0) else None
  | PtIntConst z, PtFloatConst t d =>
      if int_in_float_exact_interval t z then dy_fold_at t dfold (dy_norm z 0) (dy_m d, dy_e d) else None
  (* float const + runtime float: SAME type -> runtime float (the const value legitimately dropped,
     exactly the int convention above) *)
  | PtFloatConst t1 _, PtRunFloat t2 | PtRunFloat t2, PtFloatConst t1 _ =>
      if numty_eqb t1 t2 then Some (PtRunFloat t2) else None
  (* any other mix (bool/str/agg, int-const with float-const of no shared type rule) -> REJECT *)
  | _, _ => None
  end.

(** A divisor that is a CONSTANT (untyped int, typed int, OR typed FLOAT) ZERO — the constant rules apply
    transitively, so [int(0)] (a typed const 0) and [float64(0)] (a typed float const 0) BOTH count like [0]:
    Go rejects constant division by zero for floats too ("division by zero").  A RUNTIME / deferred divisor is
    NOT a constant zero (runtime div-by-zero is a panic, not a compile error — GoSem's concern).  [is_neg_const]
    (shift counts) stays INT-only — shifts gate out floats before reaching it. *)
Definition is_zero_const (c : PTy) : bool :=
  match c with
  | PtIntConst z | PtTIntConst _ z => Z.eqb z 0
  | PtFloatConst _ d => Z.eqb (dy_m d) 0   (* a typed FLOAT zero [float64(0)] — sealed-normalized, so zero iff the mantissa is 0 *)
  | _ => false
  end.
Definition is_neg_const  (c : PTy) : bool := match int_const_val c with Some z => Z.ltb z 0 | None => false end.
(* Go: an UNTYPED constant SHIFT COUNT must be representable by [uint]; the model uses its
   conservative platform-[uint] window ([int_const_repr _ GTUint] — the SAME 32-bit-safe authority
   as every platform-const range, so an admitted count compiles on 32-bit targets too).  A TYPED
   constant count is an ordinary integer operand — its own width already bounds it (a [uint64]
   count > 2^32 is valid Go on every platform; go-run-verified 0). *)
Definition untyped_count_overflow (c : PTy) : bool :=
  match c with PtIntConst b => negb (int_const_repr b GTUint) | _ => false end.

(** THE NUMERIC BINOP TYPE-CHECKER — single authority for [* / % << >> & &^ + - | ^].  Enforces, structurally:
    - [%], [&], [|], [^], [&^] and the shifts require INTEGER operands (a FLOAT operand — const or runtime —
      is rejected by the [is_int_cat] gate, closing [float64(1) % float64(2)] / [float64(1) << 2]);
    - [/] and [%] reject a CONSTANT-ZERO divisor (incl. a TYPED const zero [int(0)] and one folded from a
      constant subexpression, [1/(int(1)-int(1))]);
    - the shifts reject a NEGATIVE constant shift count ([1 << int(-1)], [1 << (-1)]) and an UNTYPED constant
      count past the conservative platform-[uint] window ([untyped_count_overflow] — Go's
      "representable by uint" count rule, 32-bit-safe), and let the count type be
      independent of the left type; the result takes the LEFT operand's TYPE, and its CONSTNESS ONLY when the
      shift COUNT is ALSO constant (a const-left/const-count shift FOLDS, repr-checked in the type; a RUNTIME
      count -> runtime of the left's type);
    - all other forms combine via [num_arith], which folds NUMERIC constants (preserving the value) and
      repr-checks typed-constant results so [int8(100)+int8(100)] is rejected. *)
Definition shfold (o : BinOp) (a b : Z) : Z := match o with BShl => Z.shiftl a b | _ => Z.shiftr a b end.
Definition num_binop (o : BinOp) (cl cr : PTy) : option PTy :=
  match o with
  | BAdd => num_arith Z.add (Some (fun a b => Some (dy_add a b))) cl cr
  | BSub => num_arith Z.sub (Some (fun a b => Some (dy_sub a b))) cl cr
  | BMul => num_arith Z.mul (Some (fun a b => Some (dy_mul a b))) cl cr
  | BDiv => if is_zero_const cr then None else num_arith Z.quot (Some dy_div) cl cr
  | BRem =>
      if andb (is_int_cat cl) (is_int_cat cr) then
        if is_zero_const cr then None else num_arith Z.rem None cl cr
      else None
  | BAnd    => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.land None cl cr else None
  | BOr     => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.lor  None cl cr else None
  | BXor    => if andb (is_int_cat cl) (is_int_cat cr) then num_arith Z.lxor None cl cr else None
  | BAndNot => if andb (is_int_cat cl) (is_int_cat cr)
               then num_arith (fun a b => Z.land a (Z.lnot b)) None cl cr else None
  | BShl | BShr =>
      if andb (is_int_cat cl) (is_int_cat cr) then
        if is_neg_const cr then None
        else if untyped_count_overflow cr then None
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
    bool — NOT [PtAgg]/[PtMap] (slice/chan/map equality is rejected; both fall through to [num_comparable] which
    is [false] on them) and NOT [PtNil] (a bare [nil == nil] is rejected; a free ident, the only thing a slice
    could be compared against, is itself rejected at [ptype]).  Numeric equality reuses [num_comparable] (so
    [int32 == int64] is rejected). *)
Definition eq_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtBool, PtBool => true
  | PtStr, PtStr => true
  | _, _ => num_comparable cl cr
  end.
(** ORDERING ([<]/[<=]/[>]/[>=]) operand check: ORDERED + mutually compatible.  Ordered = numeric / string —
    NOT bool (so [(1==1) < (2==2)] is rejected) and NOT [PtAgg]/[PtMap]/[PtNil] (slice / map / nil ordering rejected). *)
Definition ord_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtStr, PtStr => true
  | _, _ => num_comparable cl cr
  end.

(** SCALAR CONVERSION [T(a)] type-checker, for a scalar type keyword [T] (its [GoTy] via [classify]).  ★The
    KEY rule for NUMERIC constants: in Go a conversion of a numeric CONSTANT is itself a TYPED numeric CONSTANT,
    so the constant rules apply TRANSITIVELY — its value must SURVIVE the conversion (so [1/int(0)],
    [uint8(int(300))], [uint8(float64(300))] are REJECTED, not silently dropped to a runtime category).
    ([string(x)] is a value-LESS [PtStr] — string constants carry no value; see the top invariant.)  So:
    - [bool(a)] needs a bool source;
    - [string(a)] a string source (or a rune-representable int CONSTANT, untyped or typed — NOT an arbitrary
      runtime int, conservative);
    - a NUMERIC target with a CONSTANT source ([PtIntConst]/[PtTIntConst]/[PtFloatConst]) yields a TYPED
      CONSTANT, with the carried VALUE [z] REPRESENTABILITY-CHECKED against [T] (to an int type -> [PtTIntConst
      T z], to a float type -> an exact-dyadic [PtFloatConst]).  This rejects [uint8(300)], [uint8(int(300))],
      [uint8(float64(300))], [int8(128)].  A float->int constant conversion is sound because a [PtFloatConst]
      carries its EXACT dyadic value (every admitting gate — int source via [int_in_float_exact_interval],
      fold via [dy_fold_at], cross-width via [float_dyadic_repr] — is exact-or-reject, never a rounded lie),
      so the integer-valued check ([dy_e >= 0]) and the int range-check are exact;
    - a NUMERIC target with a RUNTIME source ([PtRunInt]/[PtRunFloat]) yields a RUNTIME value (runtime
      conversions truncate/round and are valid — NO representability constraint), so [int64(len([]int{1}))],
      [uint8(len([]int{1}))] (whose inner [len …] is a runtime int) stay admitted; (a runtime source can only
      arise from [len] of a slice/chan/map aggregate ([PtAgg]/[PtMap]) or [cap] of a slice/chan aggregate
      ([PtAgg] only) now — a FREE ident like [x] is rejected upstream at [ptype]);
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
      | PtIntConst z | PtTIntConst _ z =>                        (* INT-CONSTANT source -> typed float const (EXACT only; the normalized interval int is always in-window, so the repr guard is defense-in-depth making EVERY [PtFloatConst] construction site guarded — the [ptype_float_const_repr] invariant is structural, not per-site analysis) *)
          if int_in_float_exact_interval t z
          then (let d := dy_make z 0 in
                if float_dyadic_repr t (dy_m d) (dy_e d)
                then Some (PtFloatConst t d) else None)
          else None
      | PtFloatConst _ d =>                                      (* FLOAT-CONSTANT source (cross-width incl.): EXACT at the TARGET width or rejected — [float32(<inexact-at-32 float64 const>)] is valid Go that ROUNDS; Fido REJECTS (quarantined) *)
          if float_dyadic_repr t (dy_m d) (dy_e d) then Some (PtFloatConst t d) else None
      | PtRunInt _ | PtRunFloat _ => Some (PtRunFloat t)         (* RUNTIME source -> runtime float *)
      | _ => None
      end
  | GTInt | GTInt64 | GTUint | GTU8 | GTI8 | GTU16 | GTI16 | GTU32 | GTI32 | GTU64 =>
      match ca with
      | PtIntConst z | PtTIntConst _ z =>                        (* INT-CONSTANT source -> typed int const, repr-checked *)
          if int_const_repr z t then Some (PtTIntConst t z) else None
      | PtFloatConst _ d =>                                      (* FLOAT-CONSTANT source: must be INTEGER-valued ([dy_e >= 0] — Go REJECTS a truncating constant conversion, [int(1.5)] is "truncated to integer"), then repr-checked *)
          if Z.leb 0 (dy_e d) then
            let z := Z.shiftl (dy_m d) (dy_e d) in
            if int_const_repr z t then Some (PtTIntConst t z) else None
          else None
      | PtRunInt _ | PtRunFloat _ => Some (PtRunInt t)           (* RUNTIME source -> runtime int *)
      | _ => None
      end
  | _ => None   (* [classify] yields only scalar keyword GoTys here; defensive *)
  end.

(** ASSIGNABILITY of a value CATEGORY to a declared element/target [GoTy] — single authority for composite
    literal elements.  An UNTYPED int CONSTANT is assignable to any numeric type it is REPRESENTABLE in (so
    [[]uint8{300}] is rejected, [[]float64{1}] accepted); a TYPED constant or RUNTIME numeric only to its OWN
    type (so [[]int{int64(1)}] and [[]uint8{int(300)}] are rejected — a typed constant is NOT untyped, its type
    must match exactly); bool/string to their type; an aggregate ([PtAgg] slice/chan or [PtMap] map) or [nil]
    element is conservatively rejected (no free ident reaches here — it is rejected at [ptype]). *)
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
  | PtAgg | PtMap | PtNil => false
  end.

(** Pairwise DISTINCTNESS of a list of integer-constant key VALUES.  A map composite literal with DUPLICATE
    CONSTANT keys ([map[int]int{1:2, 1:3}]) is a COMPILE error in Go — Go folds constant keys and forbids
    repeats (https://go.dev/ref/spec#Composite_literals) — so [ptype]'s [EMapLit] arm rejects it.  [true] iff
    every element is unique. *)
Fixpoint nodup_z (l : list Z) : bool :=
  match l with
  | nil => true
  | x :: r => andb (negb (existsb (Z.eqb x) r)) (nodup_z r)
  end.

(** The SUPPORTED-TYPE gate — the single recursive authority every [ptype] arm that ADMITS a type
    ([ESliceLit] / [EMapLit] / the [EConv] aggregate conversions) consults.  Deliberately NOT named
    "valid" (naming is a correctness claim): its accept-set is a strict SUBSET of valid Go, and its
    rejections span TWO distinct classes that must never be conflated:
    - INVALID Go — a NON-COMPARABLE map KEY (https://go.dev/ref/spec#Map_types: [map[[]int]int] is a
      compile error), which may hide at ANY depth ([map[int]map[[]int]int{}] is invalid even EMPTY, where
      no entry check sees it).  Rejecting these is the SOUNDNESS side ([GoSafe.bad_programs]).
    - VALID Go, outside the core — pointer / chan map keys (comparable in Go) — conservatively rejected:
      fail-loud INCOMPLETENESS, quarantined in [GoSafe.valid_unsupported_programs] with a fixture on EVERY
      rejecting surface — the CARTESIAN [GoSafe.ptrchan_key_quarantine]: root literal (int-only key
      restriction), nested map value type, slice element type, and the CTSlice/CTChan/CTMap nil
      conversions.
    [GTNamed] map keys are also rejected, but they are NOT a quarantinable valid class HERE: the closed
    world has no type declarations, so no closed program can validly name one — a named key type never
    reaches this gate from valid closed source.
    SOUND direction: every type this gate ACCEPTS is valid Go — an accepted map key is a comparable
    SCALAR keyword type ([goty_key_supported], the supported subset of Go's comparable key types). *)
Definition goty_key_supported (t : GoTy) : bool :=
  match t with
  | GTPtr _ | GTSlice _ | GTChan _ | GTMap _ _ | GTNamed _ => false
  | _ => true
  end.
Fixpoint goty_supported (t : GoTy) : bool :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => goty_supported u
  | GTMap k v => goty_key_supported k && goty_supported v
  | _ => true
  end.

(** The integer-constant KEY-VALUE list of a map literal's entries, parametrized by the classifier so it can
    be the ONE spelling both inside [ptype]'s [EMapLit] arm (which must pass the still-being-defined [ptype]
    recursively) and — instantiated as [map_key_vals] below — in GoSem's evaluator and proofs. *)
Definition map_key_vals_with (pt : GExpr -> option PTy) (kvs : list (GExpr * GExpr)) : list Z :=
  flat_map (fun kv => match kv with
                      | (k, _) =>
                          match pt k with
                          | Some ck => match int_const_val ck with Some z => z :: nil | None => nil end
                          | None => nil
                          end
                      end) kvs.

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

(** [ptype]: the structural TYPE-CATEGORY assignment ([None] = structurally ill-typed / out-of-scope, rejected).
    Scope is realized in the [EId] case — only the predeclared [nil] (-> [PtNil], admitted only as a slice/chan
    conversion operand); every other identifier is undefined -> rejected.  Posture + tightening discipline: the
    TOP INVARIANT above. *)
Fixpoint ptype (e : GExpr) : option PTy :=
  match e with
  | EId i =>
      (* SCOPE, via the ONE recognized-name table: only the predeclared [nil] is a VALUE here; a
         recognized type keyword / builtin name is not a value in this position, and every other
         identifier is undefined — all rejected (exhaustive arms so a new [SpecialName] forces
         this consumer). *)
      match special_ident (proj1_sig i) with
      | Some SnNil => Some PtNil
      | Some (SnType _) | Some SnLen | Some SnCap
      | Some SnPrintln | Some SnPrint | Some SnPanic => None
      | None => None
      end
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
                    | PtFloatConst t d =>                      (* sign flip — exact; resealed via [dy_make] and REPR-GUARDED like every construction site (the window is symmetric, so the guard never fires — defense-in-depth for [ptype_float_const_repr]) *)
                        let d' := dy_make (Z.opp (dy_m d)) (dy_e d) in
                        if float_dyadic_repr t (dy_m d') (dy_e d') then Some (PtFloatConst t d') else None
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
      match ptype a with
      | None => None
      | Some ca =>
          (* the call HEAD, via the ONE recognized-name table (exhaustive arms so a new
             [SpecialName] forces this consumer): *)
          match special_ident (proj1_sig i) with
          | Some SnLen =>
              match a, ca with
              | EStr s, _ => Some (PtIntConst (Z.of_nat (String.length s)))   (* [len] of a STRING LITERAL ([EStr]) is itself a CONSTANT (its byte count) — Go folds it; modelling it as a runtime int would wrongly certify e.g. [int8(len("..")+200)] (a const-202->int8 overflow Go REJECTS).  A NON-literal string const ([string(65)], ["a"+"b"]) has no [EStr] to measure, so it hits the [_, _ => None] reject below (fail-loud). *)
              | _, (PtAgg | PtMap) => Some (PtRunInt GTInt)                   (* [len] of a slice/chan/map aggregate: a runtime int (aggregates are not constants).  [len] IS valid on a map (unlike [cap]) *)
              | _, _ => None                                                  (* a non-literal string ([string(x)]…): cannot soundly fold its length here — reject (fail-loud) *)
              end
          | Some SnCap =>
              match ca with PtAgg => Some (PtRunInt GTInt) | _ => None end    (* cap: slice/chan aggregate ONLY — NOT string, and NOT a map ([PtMap] -> None: Go forbids [cap] of a map) *)
          | Some (SnType t) => conv_to_scalar ca t                            (* a scalar conversion T(a) *)
          | Some SnNil | Some SnPrintln | Some SnPrint | Some SnPanic => None (* not VALUE-position call heads ([println]/[print]/[panic] are statement-position callees — GoSafe's concern; [nil] is not callable) *)
          | None => None                                                      (* unknown function: REJECT *)
          end
      end
  | ECall _ _ => None
  | EConv c e0 =>
      match c with
      | CTMap _ _ => None                 (* a MAP conversion is QUARANTINED — the TARGET type is wholly unchecked here; a future admission must consult [goty_supported] on the WHOLE target, FORCED by GoSafe's gated ∀-theorem [ctmap_conv_unsupported_target_rejected].  Even the VALID [map[K]V(nil)] is rejected (pinned in [GoSafe.valid_unsupported_programs]); invalid-target witnesses (root / nested / slice-wrapped key) in [GoSafe.bad_programs] *)
      | CTSlice _ | CTChan _ =>
          (* an aggregate conversion is admitted ONLY for the predeclared [nil] operand ([[]int(nil)]) and a
             SUPPORTED target type ([goty_supported] — [[]map[[]int]int(nil)] hides an invalid map key;
             valid-but-out-of-core key types are rejected the same way); a KNOWN
             aggregate/scalar operand — or a free ident (now rejected upstream) — is REJECTED
             ([chan int([]int{1})], mismatched conversions) *)
          if goty_supported (convty_ty c)
          then match ptype e0 with Some PtNil => Some PtAgg | _ => None end
          else None
      end
  | EIndex (ESliceLit t es) idx =>
      (* indexing a slice LITERAL directly by an INTEGER index.  For a SLICE, gc compile-checks a CONSTANT index
         only for NON-NEGATIVE + INT-REPRESENTABLE (verified: gc rejects [[]int{..}[-1]] "must not be negative"
         and [..[2^63]] "overflows int", but ACCEPTS an OOB positive [[]int{10,20}[5]] — OOB is a RUN-TIME PANIC,
         NOT a compile error, unlike an ARRAY).  So reject a negative / non-int-representable constant (against
         Fido's CONSERVATIVE [GTInt] = 32-bit min, so a huge index valid only on a 64-bit gc is fail-CLOSED
         rejected — safe incompleteness); accept an OOB-but-representable constant, OR any RUNTIME (non-constant)
         integer index (its bounds — incl. OOB — are behavioral, deferred to B3).  Brick 1: INTEGER elem types. *)
      if is_int_goty t
         && forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es
      then match ptype idx with
           | Some ci =>
               if is_int_cat ci then
                 match int_const_val ci with
                 | Some k => if (0 <=? k)%Z && int_const_repr k GTInt then Some (PtRunInt t) else None
                 | None   => Some (PtRunInt t)   (* runtime integer index: bounds (incl. OOB) are behavioral (B3) *)
                 end
               else None
           | None => None
           end
      else None
  | ESliceLit t es =>
      if goty_supported t
         && forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es
      then Some PtAgg else None
  | EMapLit kt vt kvs =>
      (* a MAP literal [map[K]V{k1:v1, ..}]: SOUNDLY supported when the key type is an INTEGER scalar, the
         value TYPE passes the supported-type gate ([goty_supported] — an invalid nested map key like
         [map[int]map[[]int]int{}] is rejected even EMPTY, where no entry check could see it), every KEY is an
         integer CONSTANT assignable to [kt], every VALUE is assignable to [vt], and the constant keys are
         PAIRWISE DISTINCT (Go forbids duplicate constant keys).  Restricting keys to integer CONSTANTS is
         what makes distinctness decidable here — their VALUE is carried ([int_const_val]); a non-integer
         comparable key (string/bool) or a runtime/non-constant key is conservatively REJECTED (fail-loud), its
         value not foldable in [PTy].  This LIFTS the old blanket quarantine to a structural check; the GoSafe
         companions [map[int]uint8{1:300}] / [map[uint8]int{300:1}] (representability), [map[int]int{1:2,1:3}]
         (distinctness), and [map[int]map[[]int]int{}] (nested validity) lock it. *)
      if andb (andb (andb (is_int_goty kt) (goty_supported vt))
                    (forallb (fun kv => match kv with
                                        | (k, v) =>
                                            match ptype k, ptype v with
                                            | Some ck, Some cv =>
                                                match int_const_val ck with
                                                | Some _ => andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                                | None => false
                                                end
                                            | _, _ => false
                                            end
                                        end) kvs))
              (nodup_z (map_key_vals_with ptype kvs))
      then Some PtMap else None
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => None
  end.

(** [map_key_vals_with] instantiated at the finished classifier — THE spelling of a map literal's constant
    key values everywhere outside [ptype]'s own arm (GoSem's evaluator and its inclusion proofs). *)
Definition map_key_vals : list (GExpr * GExpr) -> list Z := map_key_vals_with ptype.



(** STRUCTURALLY-supported VALUE expression — [ptype] accepts it (well-typed by REFINED
    category).  Closed type errors of the PINNED classes are rejected — shape errors,
    numeric/structural errors, FREE identifiers ([ptype (EId _) = None]) — fixture-backed
    in [GoSafe.bad_programs], NOT a universal rejection theorem.  Accepted: [EInt], well-typed
    binops/unops/conversions; [len] of a string LITERAL (folds to the byte count) or of a
    slice/chan/map aggregate; [cap] of a slice/chan aggregate ONLY (Go forbids [cap] of a
    map); a slice literal with [goty_supported] element type and ASSIGNABLE elements; an
    INTEGER-indexed access into an INTEGER slice literal (a NEGATIVE constant index is
    rejected — gc compile error; one beyond the CONSERVATIVE 32-bit [GTInt] is
    over-rejected fail-closed; an OOB POSITIVE constant is VALID Go — run-time panic — so
    supported); an INTEGER-key map LITERAL with [goty_supported] value type, DISTINCT
    assignable constant keys, assignable values ([map[K]V(x)] conversions stay quarantined
    — sealed by [GoSafe.ctmap_conv_unsupported_target_rejected]).  [len] of a NON-literal
    string is rejected (its const length is not folded here).  ★[PtNil] is NOT a value —
    bare [_ = nil] is "use of untyped nil"; [nil] is a value only inside a slice/chan
    conversion.  ★DEFAULT-[int] BOUNDARY: a bare untyped int constant used as a value must
    fit the CONSERVATIVE 32-bit range (sound on every Go target); a typed constant was
    already range-checked at its conversion. *)
(** The VALUE-position discipline as a CATEGORY predicate (shared by the closed [svalue] and the
    scope-aware statement checks — one per-category authority, no twin spelling): a bare untyped
    int constant must fit the conservative default [int]; a bare [nil] is "use of untyped nil";
    every other assigned category is a value. *)
Definition svalue_cat (c : PTy) : bool :=
  match c with
  | PtIntConst z => int_const_repr z GTInt   (* default-[int] boundary: bare untyped const must fit int *)
  | PtNil => false   (* a bare [nil] value is "use of untyped nil" — invalid; [nil] is a value only inside a conversion *)
  | PtTIntConst _ _ | PtFloatConst _ _ | PtRunInt _ | PtRunFloat _
  | PtBool | PtStr | PtAgg | PtMap => true
  end.
Definition svalue (e : GExpr) : bool :=
  match ptype e with
  | Some c => svalue_cat c
  | None => false
  end.
Arguments svalue_cat !c /.
