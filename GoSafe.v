(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; see ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate — a supported-subset check — NOT behavioral safety, and it
    is NAMED so deliberately (naming is a correctness claim: never call a syntactic gate "Safe").  The
    semantic [BehaviorSafe] (no nil-deref / OOB / send-on-closed / illegal-close / data-race / …, defined over
    GoSem) lands once GoSem is the ONE authoritative semantics — at which point the blessed path becomes
    emit_safe over a [SafeProgram] (= EmittableProgram + BehaviorSafe).  Until then GoEmit emits only the
    SUPPORTED subset via emit_supported, and must NOT be described as behaviorally safe.
    ============================================================================ *)
From Fido Require Import GoAst GoPrint.   (* GoPrint for [classify] : the keyword -> GoTy map (scalar conversions) *)
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ---- A STRUCTURAL TYPE-CATEGORY for the supported expression subset ([ptype]) ----
    The supportedness gate must NOT certify INVALID Go.  A purely shape-based [svalue] leaked TYPE side
    conditions; an under-refined [ptype] (a single fat [PtNum] / a single comparison rule / a shared
    [len]=[cap] rule / a shape-only aggregate conversion) STILL leaked numeric and structural side conditions:
    float modulo / float shift ([float64(1) % float64(2)], [float64(1) << 2]), constant overflow
    ([uint8(300)], [[]uint8{300}]), mixed fixed-width arithmetic ([int64(3) + int32(2)]), bool ordering
    ([(1==1) < (2==2)]), slice equality/ordering, [cap] of a string ([cap(string(x))]), and invalid aggregate
    conversions ([chan int([]int{1})]) all sailed through.  [ptype] now assigns each expression a REFINED
    structural TYPE CATEGORY, or REJECTS it ([None]) as structurally ill-typed.  The refinement is exactly
    enough to make every obligation STRUCTURAL: integers are split from floats; an UNTYPED INTEGER CONSTANT
    carries its VALUE (a [Z]) so representability/overflow and division/shift-by-zero are decided from the
    value (constant subexpressions are FOLDED, so [1 / (1 - 1)] is caught); a TYPED numeric carries its [GoTy]
    so mixed-width arithmetic is rejected; aggregates ([PtAgg]) are a valid value but never numeric/printable.
    ONLY a genuinely-unknown IDENTIFIER is DEFERRED ([PtUnk] — its type/scope is GoSem's job).
    ★INVARIANT — for a CLOSED expression (no [EId]), [ptype] never returns [Some _] for a form Go's type
    checker rejects: it is MAXIMALLY CONSERVATIVE, rejecting much VALID Go too (any conversion of a KNOWN
    aggregate, [string] of a typed int, const+typed when not representable, nested-aggregate elements), which
    is the correct posture — a smaller SOUND supported subset.  The deferral of [PtUnk] is the ONLY admission
    of an unproven form, and it fires only where the operand is an actual deferred identifier.  (A full
    typed/scoped check is GoSem.) *)
Inductive PTy : Type :=
  | PtIntConst (z : Z)   (* an UNTYPED INTEGER CONSTANT — value known, type not yet fixed (adapts on use) *)
  | PtInt   (t : GoTy)   (* a TYPED integer value (t a fixed/platform integer GoTy) — runtime, not a foldable const *)
  | PtFloat (t : GoTy)   (* a TYPED float value (t = GTFloat64 / GTFloat32) *)
  | PtBool
  | PtStr
  | PtAgg    (* a slice/chan aggregate value: a valid VALUE, but never numeric / order-comparable / printable *)
  | PtUnk.   (* an identifier — type DEFERRED (could be anything; scope/GoSem decides) *)

(** ---- numeric-type predicates over [GoTy] (the scalar numeric constructors) ---- *)
Definition is_int_goty (t : GoTy) : bool :=
  match t with
  | GTInt | GTInt64 | GTUint | GTU8 | GTI8 | GTU16 | GTI16 | GTU32 | GTI32 | GTU64 => true
  | _ => false
  end.
Definition is_float_goty (t : GoTy) : bool :=
  match t with GTFloat64 | GTFloat32 => true | _ => false end.
(** Decidable equality on the numeric SCALAR [GoTy]s (all [PtInt]/[PtFloat] ever carry).  Total: any pair of
    DIFFERENT (or non-numeric) constructors is [false].  Used to forbid mixed-width arithmetic/assignment. *)
Definition numty_eqb (a b : GoTy) : bool :=
  match a, b with
  | GTInt, GTInt | GTInt64, GTInt64 | GTUint, GTUint
  | GTU8, GTU8 | GTI8, GTI8 | GTU16, GTU16 | GTI16, GTI16
  | GTU32, GTU32 | GTI32, GTI32 | GTU64, GTU64
  | GTFloat64, GTFloat64 | GTFloat32, GTFloat32 => true
  | _, _ => false
  end.

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
(** an int constant is representable as a FLOAT (conservatively) iff it fits in int64 — far inside the finite
    float64/float32 range, so the const->float conversion never overflows.  (Larger constants are rejected.) *)
Definition int_repr_as_float (z : Z) : bool := int_const_repr z GTInt64.

(** ---- numeric CATEGORY predicates ---- *)
Definition is_int_cat   (c : PTy) : bool := match c with PtIntConst _ | PtInt _ => true | _ => false end.
Definition is_float_cat (c : PTy) : bool := match c with PtFloat _ => true | _ => false end.
Definition is_num_cat   (c : PTy) : bool := orb (is_int_cat c) (is_float_cat c).
Definition is_int_or_unk  (c : PTy) : bool := match c with PtIntConst _ | PtInt _ | PtUnk => true | _ => false end.
Definition is_bool_or_unk (c : PTy) : bool := match c with PtBool | PtUnk => true | _ => false end.

(** NUMERIC COMPATIBILITY — single authority for arithmetic + numeric-comparison operand checking: can two
    numeric categories combine?  [PtUnk] defers but ONLY against a numeric (so [x + true] is rejected: [bool]
    is not numeric); two untyped consts always combine; a const combines with a typed numeric iff
    REPRESENTABLE in it (so [int8(1) + 300] is rejected); two typed numerics combine iff SAME type (so
    [int64(3) + int32(2)] and [float64 + float32] are rejected).  bool/str/agg pairs never combine here. *)
Definition num_compatible (cl cr : PTy) : bool :=
  match cl, cr with
  | PtUnk, PtUnk => true
  | PtUnk, c | c, PtUnk => is_num_cat c
  | PtIntConst _, PtIntConst _ => true
  | PtIntConst z, PtInt t | PtInt t, PtIntConst z => int_const_repr z t
  | PtIntConst z, PtFloat _ | PtFloat _, PtIntConst z => int_repr_as_float z
  | PtInt t1, PtInt t2 => numty_eqb t1 t2
  | PtFloat t1, PtFloat t2 => numty_eqb t1 t2
  | _, _ => false
  end.

(** RESULT CATEGORY of a numeric binop for COMPATIBLE operands that are NOT both untyped constants (the
    both-const case folds a VALUE, handled per-op in [num_binop]).  A typed operand fixes the result type;
    const+typed yields the typed type; unk+const stays deferred. *)
Definition combine_typed (cl cr : PTy) : option PTy :=
  match cl, cr with
  | PtUnk, PtUnk => Some PtUnk
  | PtUnk, PtInt t | PtInt t, PtUnk => Some (PtInt t)
  | PtUnk, PtFloat t | PtFloat t, PtUnk => Some (PtFloat t)
  | PtUnk, PtIntConst _ | PtIntConst _, PtUnk => Some PtUnk
  | PtInt t, _ | _, PtInt t => Some (PtInt t)
  | PtFloat t, _ | _, PtFloat t => Some (PtFloat t)
  | _, _ => None
  end.

(** THE NUMERIC BINOP TYPE-CHECKER — single authority for [* / % << >> & &^ + - | ^].  Enforces, structurally:
    - [%], [&], [|], [^], [&^] and the shifts require INTEGER operands (a FLOAT operand is rejected — closing
      [float64(1) % float64(2)] / [float64(1) << 2]);
    - [/] and [%] reject a CONSTANT-ZERO divisor (incl. one folded from a constant subexpression, [1/(1-1)]);
    - the shifts reject a NEGATIVE constant shift count and let the operand types differ (the count type is
      independent), the result taking the LEFT type;
    - all other forms demand [num_compatible] and combine via [combine_typed]; two untyped constants FOLD to a
      new untyped constant (so downstream representability sees the real value). *)
Definition is_zero_const (c : PTy) : bool := match c with PtIntConst z => Z.eqb z 0 | _ => false end.
Definition is_neg_const  (c : PTy) : bool := match c with PtIntConst z => Z.ltb z 0 | _ => false end.
Definition num_binop (o : BinOp) (cl cr : PTy) : option PTy :=
  match o with
  | BAdd | BSub | BMul =>
      if num_compatible cl cr then
        match cl, cr with
        | PtIntConst a, PtIntConst b =>
            Some (PtIntConst (match o with BAdd => Z.add a b | BSub => Z.sub a b | _ => Z.mul a b end))
        | _, _ => combine_typed cl cr
        end
      else None
  | BDiv =>
      if is_zero_const cr then None
      else if num_compatible cl cr then
        match cl, cr with
        | PtIntConst a, PtIntConst b => Some (PtIntConst (Z.quot a b))
        | _, _ => combine_typed cl cr
        end
      else None
  | BRem =>
      if andb (is_int_or_unk cl) (is_int_or_unk cr) then
        if is_zero_const cr then None
        else if num_compatible cl cr then
          match cl, cr with
          | PtIntConst a, PtIntConst b => Some (PtIntConst (Z.rem a b))
          | _, _ => combine_typed cl cr
          end
        else None
      else None
  | BAnd | BOr | BXor | BAndNot =>
      if andb (is_int_or_unk cl) (is_int_or_unk cr) then
        if num_compatible cl cr then
          match cl, cr with
          | PtIntConst a, PtIntConst b =>
              Some (PtIntConst (match o with
                                | BAnd => Z.land a b | BOr => Z.lor a b
                                | BXor => Z.lxor a b | _ => Z.land a (Z.lnot b) end))
          | _, _ => combine_typed cl cr
          end
        else None
      else None
  | BShl | BShr =>
      if andb (is_int_or_unk cl) (is_int_or_unk cr) then
        if is_neg_const cr then None
        else match cl, cr with
             | PtIntConst a, PtIntConst b =>
                 Some (PtIntConst (match o with BShl => Z.shiftl a b | _ => Z.shiftr a b end))
             | _, _ => match cl with
                       | PtInt t => Some (PtInt t)
                       | PtIntConst _ => Some (PtInt GTInt)   (* 1 << x : the untyped 1 defaults to int *)
                       | PtUnk => Some PtUnk
                       | _ => None
                       end
             end
      else None
  | _ => None    (* the comparison / logical binops are not numeric — handled in [ptype] *)
  end.

(** EQUALITY ([==]/[!=]) operand check: COMPARABLE + mutually compatible.  Comparable = numeric / string /
    bool / deferred — NOT [PtAgg] (slice/map/func equality is rejected; a slice may only be compared with
    nil, which appears as a deferred ident).  Numeric equality reuses [num_compatible] (so [int32 == int64]
    is rejected). *)
Definition eq_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtUnk, _ | _, PtUnk => true
  | PtBool, PtBool => true
  | PtStr, PtStr => true
  | _, _ => num_compatible cl cr
  end.
(** ORDERING ([<]/[<=]/[>]/[>=]) operand check: ORDERED + mutually compatible.  Ordered = numeric / string /
    deferred — NOT bool (so [(1==1) < (2==2)] is rejected) and NOT [PtAgg] (slice ordering rejected). *)
Definition ord_comparable (cl cr : PTy) : bool :=
  match cl, cr with
  | PtStr, PtStr => true
  | PtStr, PtUnk | PtUnk, PtStr => true
  | PtUnk, PtUnk => true
  | _, _ => num_compatible cl cr
  end.

(** SCALAR CONVERSION [T(a)] type-checker, for a scalar type keyword [T] (its [GoTy] via [classify]).  Each
    target enforces its own rule: [bool(a)] needs a bool/deferred source; [string(a)] a string/deferred (or a
    rune-representable int CONSTANT — NOT an arbitrary int, conservative); a numeric target admits a
    numeric/deferred source (a runtime numeric converts freely), but an int CONSTANT must be REPRESENTABLE in
    the target (so [uint8(300)] is rejected).  bool/string/aggregate sources to a numeric target are rejected
    (so [int([]int{1})] / [int(true)] fail). *)
Definition conv_to_scalar (ca : PTy) (t : GoTy) : option PTy :=
  match t with
  | GTBool => match ca with PtBool | PtUnk => Some PtBool | _ => None end
  | GTString =>
      match ca with
      | PtStr | PtUnk => Some PtStr
      | PtIntConst z => if int_const_repr z GTI32 then Some PtStr else None   (* string(rune const) *)
      | _ => None
      end
  | GTFloat64 | GTFloat32 =>
      match ca with
      | PtIntConst z => if int_repr_as_float z then Some (PtFloat t) else None
      | PtInt _ | PtFloat _ | PtUnk => Some (PtFloat t)
      | _ => None
      end
  | GTInt | GTInt64 | GTUint | GTU8 | GTI8 | GTU16 | GTI16 | GTU32 | GTI32 | GTU64 =>
      match ca with
      | PtIntConst z => if int_const_repr z t then Some (PtInt t) else None
      | PtInt _ | PtFloat _ | PtUnk => Some (PtInt t)
      | _ => None
      end
  | _ => None   (* [classify] yields only scalar keyword GoTys here; defensive *)
  end.

(** ASSIGNABILITY of a value CATEGORY to a declared element/target [GoTy] — single authority for composite
    literal elements.  An untyped int CONSTANT is assignable to any numeric type it is REPRESENTABLE in (so
    [[]uint8{300}] is rejected, [[]float64{1}] accepted); a TYPED numeric only to its OWN type (so
    [[]int{int64(1)}] is rejected); bool/string to their type; a deferred ident to anything; an aggregate
    element is conservatively rejected. *)
Definition assignable_to_ty (ce : PTy) (t : GoTy) : bool :=
  match ce with
  | PtUnk => true
  | PtIntConst z =>
      if is_int_goty t then int_const_repr z t
      else if is_float_goty t then int_repr_as_float z
      else false
  | PtInt t' => if is_int_goty t then numty_eqb t' t else false
  | PtFloat t' => if is_float_goty t then numty_eqb t' t else false
  | PtBool => match t with GTBool => true | _ => false end
  | PtStr  => match t with GTString => true | _ => false end
  | PtAgg  => false
  end.

(** [ptype]: the structural TYPE-CATEGORY assignment.  [None] = structurally ill-typed (rejected). *)
Fixpoint ptype (e : GExpr) : option PTy :=
  match e with
  | EId _ => Some PtUnk
  | EInt z => Some (PtIntConst z)
  | EBn o l r =>
      match ptype l, ptype r with
      | Some cl, Some cr =>
          match o with
          | BMul|BDiv|BRem|BShl|BShr|BAnd|BAndNot|BAdd|BSub|BOr|BXor => num_binop o cl cr
          | BEq|BNe => if eq_comparable cl cr then Some PtBool else None
          | BLt|BLe|BGt|BGe => if ord_comparable cl cr then Some PtBool else None
          | BLAnd|BLOr => if andb (is_bool_or_unk cl) (is_bool_or_unk cr) then Some PtBool else None
          end
      | _, _ => None
      end
  | EUn o e0 =>
      match ptype e0 with
      | Some c =>
          match o with
          | UNeg => match c with                              (* unary minus: int or float *)
                    | PtIntConst z => Some (PtIntConst (Z.opp z))
                    | PtInt t => Some (PtInt t) | PtFloat t => Some (PtFloat t)
                    | PtUnk => Some PtUnk | _ => None end
          | UXor => match c with                              (* bitwise complement: INTEGER only (no float) *)
                    | PtIntConst z => Some (PtIntConst (Z.lnot z))
                    | PtInt t => Some (PtInt t)
                    | PtUnk => Some PtUnk | _ => None end
          | UNot => match c with PtBool | PtUnk => Some PtBool | _ => None end
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
          then match ca with PtStr | PtAgg | PtUnk => Some (PtInt GTInt) | _ => None end   (* len: string OR aggregate *)
          else if String.eqb fn "cap"
          then match ca with PtAgg | PtUnk => Some (PtInt GTInt) | _ => None end            (* cap: aggregate ONLY (NOT string) *)
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
          (* an aggregate conversion is admitted ONLY for a DEFERRED operand ([[]int(nil)]); a KNOWN
             aggregate/scalar operand is REJECTED ([chan int([]int{1})], mismatched conversions) *)
          match ptype e0 with Some PtUnk => Some PtAgg | _ => None end
      end
  | ESliceLit t es =>
      if forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es
      then Some PtAgg else None
  | EMapLit _ _ _ => None                 (* a MAP literal is QUARANTINED (comparable-key TYPE + assignability not structural) *)
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => None
  end.

(** STRUCTURALLY-supported VALUE expression — [ptype] accepts it (well-typed by REFINED category; only unknown
    idents are deferred).  So a closed type-error is REJECTED — not just the shape errors ([len(1)] / [1 && 2]
    / [int([]int{1})] / [map[..]..{..}]) but the numeric/structural ones too ([float64(1) % float64(2)],
    [uint8(300)], [int64(3)+int32(2)], slice/bool comparison, [cap(string(x))], [chan int([]int{1})]) — while
    [EInt], an ident (scope deferred), well-typed binops/unops/conversions, [len] of a string-or-aggregate,
    [cap] of an aggregate, and a slice literal whose elements are ASSIGNABLE to its element type are admitted.
    STRUCTURAL only: it cannot check SCOPE (an undefined ident) — that is GoSem. *)
Definition svalue (e : GExpr) : bool := match ptype e with Some _ => true | None => false end.

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
    category (a numeric — [PtIntConst]/[PtInt]/[PtFloat] — or [PtBool]/[PtStr]).  This reuses the structural
    type-checker, so it INHERITS its rejection of closed type-errors — e.g. [len(1)] (an int is not len-able),
    [bool(1)], [1 && 2], [!1], [int([]int{1})], [float64(1) % float64(2)], [uint8(300)] — and of non-scalars
    ([PtAgg] slice/chan literals and conversions) and of bare identifiers ([PtUnk], unknown type): emit those
    via [_ = <value>] instead.  ([println(int(x))] / [println(len(x))] stay admitted: a conversion / [len]
    result category is KNOWN even when the operand is a deferred ident.) *)
Definition printable_arg_ok (e : GExpr) : bool :=
  match ptype e with
  | Some (PtIntConst _) | Some (PtInt _) | Some (PtFloat _) | Some PtBool | Some PtStr => true
  | _ => false
  end.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec a bare expression statement must be a
    CALL (a plain value [1] / [a + b] is "evaluated but not used"), AND — crucially — a genuine function call,
    NOT a CONVERSION ([int(x)] is a conversion, also invalid as a statement).  Since no user functions exist
    yet, the statement-valid callees are EXACTLY the whitelisted builtins at their correct arity
    ([stmt_call_ok]).  ARGUMENTS are checked PER BUILTIN: [print]/[println] admit only the guaranteed-printable
    SCALAR subset ([printable_arg_ok] — NOT arbitrary [svalue], so [println(<slice/map>)] / aggregate printing
    is excluded as implementation-defined); [panic] admits any [svalue] (it takes an [interface{}]).  So
    [int(x)] / [Foo(x)] / [1()] / [len(x)] / [panic()] / [println([]int{1})] as statements are all rejected;
    [println(int(x))] / [println(1 + 2)] / [panic(x)] are accepted. *)
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
    print them.  SCOPE OF THE CLAIM (kept honest): this is STRUCTURAL/grammatical supportedness — it does NOT,
    and syntactically cannot, check SCOPE (an undefined identifier) or TYPES (a mismatch); those are the
    GoSem/type-checker layer ([BehaviorSafe], later).  So it is SUPPORTEDNESS, not "guaranteed-compiling" and
    not behavioral safety.  (The package-name-ONLY check was too weak — it certified invalid Go — now fixed.) *)
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

(** POSITIVE — a conversion IS fine in VALUE position: `func main(){ println(int(x)) }` is supported (the
    statement is a [println] call; its argument [int(x)] is a conversion, a valid [svalue]).  This pins the
    value-vs-statement asymmetry the [int(x)]-statement regression above relies on. *)
Definition supported_conv_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "int" eq_refl)) [EId (mkIdent "x" eq_refl)]])].
Example conv_arg_supported : SupportedProgram supported_conv_arg.
Proof. reflexivity. Qed.

(** POSITIVE (Phase 4, [EConv]) — a slice/chan type-FORM conversion is a VALUE, used via [_ = ...]: `func
    main(){ _ = []int(x) }` is supported ([[]int(x)] is an [EConv], a valid [svalue]).  As an AGGREGATE it is
    NOT a [println] arg (that printing is implementation-defined — see [printable_arg_ok]): `func main(){
    println([]int(x)) }` is rejected.  A bare [EConv] statement `func main(){ []int(x) }` is also rejected
    ([expr_stmt_ok] admits only [ECall (EId _) _]). *)
Definition supported_conv_composite_arg : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl)))].
Example conv_composite_arg_supported : SupportedProgram supported_conv_composite_arg.
Proof. reflexivity. Qed.
Definition unsupported_conv_composite_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl)))].
Example conv_composite_stmt_unsupported : supported_program unsupported_conv_composite_stmt = false.
Proof. reflexivity. Qed.
Fail Example conv_composite_stmt_supported : SupportedProgram unsupported_conv_composite_stmt := eq_refl.
(** [println] of a slice/aggregate is NOT supported (implementation-defined printing). *)
Definition unsupported_println_aggregate : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl))])].
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
    A NEGATIVE constant shift count is rejected even with a deferred left operand. *)
Example bad_div_zero : supported_program (pl_arg (EBn BDiv (EInt 1) (EInt 0))) = false.
Proof. reflexivity. Qed.
Example bad_div_zero_folded : supported_program (pl_arg (EBn BDiv (EInt 1) (EBn BSub (EInt 1) (EInt 1)))) = false.
Proof. reflexivity. Qed.
Example bad_mod_zero : supported_program (pl_arg (EBn BRem (EInt 1) (EInt 0))) = false.
Proof. reflexivity. Qed.
Example bad_neg_shift : supported_program (pl_arg (EBn BShl gs_x (EInt (-1)))) = false.
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

(** FINDING 3 — [len]/[cap] separated.  [cap] of a STRING is rejected ([cap(string(65))], and the cleaner
    [cap(string(x))] where [string(x)] is a genuine deferred-source string); [len] of a string stays OK. *)
Example bad_cap_string_lit : supported_program (gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [gs_str (EInt 65)])) = false.
Proof. reflexivity. Qed.
Example bad_cap_string : supported_program (gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [gs_str gs_x])) = false.
Proof. reflexivity. Qed.
Example ok_len_string : SupportedProgram (pl_arg (ECall (EId (mkIdent "len" eq_refl)) [gs_str gs_x])).
Proof. reflexivity. Qed.

(** FINDING 4 — aggregate conversion soundness.  A slice->chan conversion of a KNOWN slice ([chan int([]int{1})])
    and a mismatched slice conversion of a KNOWN slice ([[]int([]string{})]) are rejected; only a DEFERRED
    operand ([[]int(nil)]) is admitted (pinned below by [conv_composite_arg_supported]). *)
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
    value-returning builtin is fine in VALUE position: `func main(){ println(len(x)) }` is supported ([len(x)]
    is an [svalue]); and `func main(){ _ = cap(x) }` likewise.  But it is FORBIDDEN in STATEMENT position
    ("len … not permitted in statement context"): `func main(){ len(x) }` is NOT supported ([stmt_call_ok]
    excludes [len]).  Arity is pinned: `func main(){ println(len(x, y)) }` is NOT supported (len takes one
    arg, so the 2-arg form is not an [svalue]).  Pins all four. *)
Definition supported_len_value : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl)) [EId (mkIdent "x" eq_refl)]])].
Example len_value_supported : SupportedProgram supported_len_value.
Proof. reflexivity. Qed.
Definition supported_cap_blank : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsBlankAssign (ECall (EId (mkIdent "cap" eq_refl)) [EId (mkIdent "x" eq_refl)])].
Example cap_blank_supported : SupportedProgram supported_cap_blank.
Proof. reflexivity. Qed.
Definition unsupported_len_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "len" eq_refl)) [EId (mkIdent "x" eq_refl)])].
Example len_stmt_unsupported : supported_program unsupported_len_stmt = false.
Proof. reflexivity. Qed.
Fail Example len_stmt_supported : SupportedProgram unsupported_len_stmt := eq_refl.
Definition unsupported_len_arity : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EId (mkIdent "println" eq_refl))
                               [ECall (EId (mkIdent "len" eq_refl))
                                      [EId (mkIdent "x" eq_refl); EId (mkIdent "y" eq_refl)]])].
Example len_arity_unsupported : supported_program unsupported_len_arity = false.
Proof. reflexivity. Qed.

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions value_stmt_unsupported.
