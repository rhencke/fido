(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; see ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate — a supported-subset check — NOT behavioral safety, and it
    is NAMED so deliberately (naming is a correctness claim: never call a syntactic gate "Safe").  The
    semantic [BehaviorSafe] (no nil-deref / OOB / send-on-closed / illegal-close / data-race / …, defined over
    GoSem) lands once GoSem is the ONE authoritative semantics — at which point the blessed path becomes
    emit_safe over a [SafeProgram] (= EmittableProgram + BehaviorSafe).  Until then GoEmit emits only the
    SUPPORTED subset via emit_supported, and must NOT be described as behaviorally safe.
    ============================================================================ *)
From Fido Require Import GoAst.
From Stdlib Require Import String List Bool ZArith.
Import ListNotations.
Open Scope string_scope.

(** ---- A STRUCTURAL TYPE-CATEGORY for the supported expression subset ([ptype]) ----
    The supportedness gate must NOT certify INVALID Go.  A purely shape-based [svalue] leaked TYPE side
    conditions — it admitted CLOSED type-errors like [len(1)] / [bool(1)] / [1 && 2] / [!1] / [int([]int{1})].
    [ptype] assigns each expression a coarse TYPE CATEGORY, or REJECTS it ([None]) as structurally ill-typed,
    so those closed errors are rejected STRUCTURALLY while only genuinely-unknown identifiers are DEFERRED
    ([PtUnk]).  It is conservative — it tracks only categories (not the exact numeric type) and admits any
    deferred operand — so it rejects some valid Go too, but NEVER admits an expression Go's type checker would
    reject from the structure alone.  (This is the type-checking the gate had been deferring; a full
    typed/scoped check is GoSem.) *)
Inductive PTy : Type :=
  | PtNum    (* a numeric value (int, uint, float, ...) — WHICH numeric is not tracked; see the arith rule *)
  | PtBool
  | PtStr
  | PtAgg    (* a non-scalar aggregate/reference value (slice/chan/ptr): a valid VALUE, not printable, not arith *)
  | PtUnk.   (* an identifier — type DEFERRED (could be anything; scope/GoSem decides) *)

Definition is_value_builtin (f : string) : bool := String.eqb f "len" || String.eqb f "cap".
(** category of a declared [GoTy] (for conversions / slice element types) *)
Definition goty_cat (t : GoTy) : PTy :=
  match t with
  | GTBool => PtBool | GTString => PtStr
  | GTPtr _ | GTSlice _ | GTChan _ | GTMap _ _ => PtAgg
  | GTNamed _ => PtUnk
  | _ => PtNum   (* GTInt / GTInt64 / GTUint / GTU8.. / GTI8.. / GTFloat* — the numeric scalars *)
  end.
(** category a SCALAR conversion [T(_)] produces (by the type-keyword name; chan/map are keywords, never
    [go_ident] callees, so only scalar keywords occur as an [EId] conversion callee). *)
Definition type_keyword_cat (s : string) : PTy :=
  if String.eqb s "bool" then PtBool else if String.eqb s "string" then PtStr else PtNum.
Definition num_or_unk (c : PTy) : bool := match c with PtNum | PtUnk => true | _ => false end.
Definition bool_or_unk (c : PTy) : bool := match c with PtBool | PtUnk => true | _ => false end.
(** is category [ce] assignable to a target/element category [tc]?  same category, or either side deferred. *)
Definition cat_assignable (ce tc : PTy) : bool :=
  match ce, tc with
  | PtUnk, _ | _, PtUnk => true
  | PtNum, PtNum | PtBool, PtBool | PtStr, PtStr | PtAgg, PtAgg => true
  | _, _ => false
  end.

Fixpoint ptype (e : GExpr) : option PTy :=
  match e with
  | EId _ => Some PtUnk
  | EInt _ => Some PtNum
  | EBn o l r =>
      match ptype l, ptype r with
      | Some cl, Some cr =>
          match o with
          | BMul|BDiv|BRem|BShl|BShr|BAnd|BAndNot|BAdd|BSub|BOr|BXor =>
              if num_or_unk cl && num_or_unk cr then Some PtNum else None     (* int arith: numeric×numeric *)
          | BEq|BNe|BLt|BLe|BGt|BGe =>
              if cat_assignable cl cr || cat_assignable cr cl then Some PtBool else None  (* compatible cmp *)
          | BLAnd|BLOr =>
              if bool_or_unk cl && bool_or_unk cr then Some PtBool else None   (* &&/||: bool×bool *)
          end
      | _, _ => None
      end
  | EUn o e0 =>
      match ptype e0 with
      | Some c => match o with
                  | UXor | UNeg => if num_or_unk c then Some PtNum else None
                  | UNot => if bool_or_unk c then Some PtBool else None
                  | UDeref | UAddr => None
                  end
      | None => None
      end
  | ECall (EId i) (a :: nil) =>
      let fn := proj1_sig i in
      match ptype a with
      | None => None
      | Some ca =>
          if is_value_builtin fn
          then match ca with PtAgg | PtStr | PtUnk => Some PtNum | _ => None end   (* len/cap: operand must be len-able *)
          else if is_type_keyword fn
          then match type_keyword_cat fn with                                       (* a scalar conversion T(a) *)
               | PtBool => match ca with PtBool | PtUnk => Some PtBool | _ => None end
               | PtStr  => match ca with PtNum | PtStr | PtUnk => Some PtStr | _ => None end  (* string(rune)/string(str) *)
               | _      => if num_or_unk ca then Some PtNum else None               (* numeric conv from numeric/unk *)
               end
          else None   (* an unknown function — its result type is unknown, REJECT *)
      end
  | ECall _ _ => None
  | EConv c e0 =>
      match c with
      | CTMap _ _ => None     (* a MAP conversion is QUARANTINED (key-type comparability not soundly structural) *)
      | CTSlice _ | CTChan _ => match ptype e0 with Some PtUnk | Some PtAgg => Some PtAgg | _ => None end
      end
  | ESliceLit t es =>
      if forallb (fun el => match ptype el with Some ce => cat_assignable ce (goty_cat t) | None => false end) es
      then Some PtAgg else None
  | EMapLit _ _ _ => None     (* a MAP literal is QUARANTINED (comparable-key TYPE + key/value assignability not structural) *)
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => None
  end.

(** STRUCTURALLY-supported VALUE expression — [ptype] accepts it (well-typed by category; only unknown idents
    are deferred).  So a closed type-error ([len(1)] / [1 && 2] / [int([]int{1})] / [map[..]..{..}]) is
    REJECTED, while [EInt], an ident (scope deferred), well-typed binops/unops/conversions, [len]/[cap] of an
    aggregate-or-unknown, and a slice literal whose elements are assignable to its element type are admitted.
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

(** A SCALAR builtin type keyword (numeric / bool / string) — [is_type_keyword] MINUS [chan]/[map] (the two
    aggregate/reference type keywords).  A conversion to such a type yields a scalar. *)
(** A [print]/[println] argument GUARANTEED-printable by the Go spec.  ★Go-spec NOTE (Bootstrapping): [print]/
    [println] are bootstrapping builtins whose implementations need NOT accept arbitrary argument types — only
    BOOLEAN, NUMERIC, and STRING are always supported.  So a printable arg is one [ptype] gives a SCALAR
    category ([PtNum]/[PtBool]/[PtStr]).  This reuses the structural type-checker, so it INHERITS its rejection
    of closed type-errors — e.g. [len(1)] ([PtNum] operand → not len-able → rejected), [bool(1)], [1 && 2],
    [!1], [int([]int{1})] — and of non-scalars ([PtAgg] slice/chan literals and conversions) and of bare
    identifiers ([PtUnk], unknown type): emit those via [_ = <value>] instead.  ([println(int(x))] /
    [println(len(x))] stay admitted: a conversion / [len] result category is KNOWN even when the operand is a
    deferred ident.) *)
Definition printable_arg_ok (e : GExpr) : bool :=
  match ptype e with Some PtNum | Some PtBool | Some PtStr => true | _ => false end.

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
