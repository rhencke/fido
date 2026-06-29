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

(** STRUCTURALLY-supported VALUE expression — the CONSERVATIVE whitelist of [GExpr] forms each guaranteed to
    PRODUCE A VALUE with NO operand-shape hazard: identifiers, integer literals, arithmetic/logical binops,
    the value-producing unary ops (!/^/-), and a builtin-type CONVERSION [T(a)].  The application case is
    restricted to a conversion ([EId] whose name is a builtin type, applied to EXACTLY ONE arg) because a
    conversion ALWAYS yields a value, whereas a general function CALL [f(args)] yields a value only if [f]
    returns one — type-dependent and unknowable here, so a void call like [println(1)] (which returns
    NOTHING) must NOT be admitted as a value (else [println(println(1))] — "used as value" — would slip
    through), and conversion arity is pinned (a conversion takes exactly one arg, so [int(1,2)] is rejected).
    The shape-CONSTRAINED forms stay out — postfix selector/index/slice/type-assertion ([1.f] / [1[0]] /
    [1[lo:hi]] / [1.(T)]) and unary deref/addr ([*1] / [&1]) — so no structural absurdity is admitted.
    STRUCTURAL only: it does NOT (and syntactically cannot) check SCOPE (an undefined identifier) or TYPES
    (e.g. [!1], convertibility of [int(x)]) — those are the GoSem/type layer. *)
Fixpoint svalue (e : GExpr) : bool :=
  match e with
  | EId _ => true
  | EInt _ => true
  | EBn _ l r => svalue l && svalue r
  | EUn o e0 => match o with UNot | UXor | UNeg => svalue e0 | UDeref | UAddr => false end
  | ECall callee args =>
      match callee, args with
      | EId i, a :: nil => is_type_keyword (proj1_sig i) && svalue a   (* a builtin-type CONVERSION [T(a)] *)
      | _, _            => false
      end
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => false
  end.

(** Builtin functions whose CALL is valid as a standalone EXPRESSION STATEMENT (Go spec: ExpressionStmt — a
    "function and method call ... can appear in statement context").  Restricted to [println] / [print]: both
    are VARIADIC, accept args of ANY type, and return NOTHING — so [print(...)] / [println(...)] are valid
    statements for ANY argument count and types, with NO arity or type hazard left unchecked.  Deliberately
    EXACT for the current AST (no user funcs / imports yet, so these are the only hazard-free statement calls).
    Excluded on purpose: CONVERSIONS ([int(x)] is not a call — invalid as a statement) and VALUE-returning
    builtins ([len(x)]/… — "evaluated but not used").  Each builtin re-enters WITH its ARITY (so an arity
    violation is rejected): [println]/[print] are VARIADIC (any arg count), [panic] takes EXACTLY ONE arg of
    ANY type (so [panic(x)] is valid for any value, but [panic()] / [panic(1,2)] are not).  ([close]/[delete]
    add a CHANNEL/MAP arg-TYPE constraint beyond arity — deferred to the GoSem/type layer.)  Widens with user
    funcs / a symbol table. *)
Definition stmt_call_ok (f : string) (args : list GExpr) : bool :=
  if String.eqb f "println" then true                                  (* variadic, any args *)
  else if String.eqb f "print" then true                               (* variadic, any args *)
  else if String.eqb f "panic" then (match args with _ :: nil => true | _ => false end)  (* exactly 1, any type *)
  else false.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec a bare expression statement must be a
    CALL (a plain value [1] / [a + b] is "evaluated but not used"), AND — crucially — a genuine function call,
    NOT a CONVERSION ([int(x)] is a conversion, also invalid as a statement).  Since no user functions exist
    yet, the statement-valid callees are EXACTLY the whitelisted builtins at their correct arity
    ([stmt_call_ok]); arguments may be any structurally-supported value [svalue] (which DOES allow a conversion
    in value position, e.g. [println(int(x))]).  So [int(x)] / [Foo(x)] / [1()] / [len(x)] / [panic()] as
    statements are all rejected. *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall (EId f) args => stmt_call_ok (proj1_sig f) args && forallb svalue args
  | _                  => false
  end.

(** A statement in the SUPPORTED subset: an expression statement must be [expr_stmt_ok]; a bare [return] is
    always fine (a valid tail of a void func like [main]). *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e => expr_stmt_ok e
  | GsReturn     => true
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
    statement ("evaluated but not used").  [int] is not in [stmt_call_builtin], so it is NOT supported. *)
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

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions value_stmt_unsupported.
