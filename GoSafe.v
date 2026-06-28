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

(** A function-NAME callee.  The ONLY call form in the supported subset (for now) is `f(args)` where [f] is an
    identifier.  This is deliberately conservative: a literal / arithmetic / slice / concrete-type-assertion
    callee is STRUCTURALLY never a function ([1(x)], [(a+b)(x)], [x.(int)(y)] are invalid Go), and the
    structurally-AMBIGUOUS callees (selector [pkg.F], index [a[i]], nested call [f()()], named-type assertion
    [x.(F)] which MIGHT be a func type) are simply DEFERRED — they re-enter, each with its own operand-shape
    check, when added.  Admitting only [EId] makes the gate obviously sound now. *)
Definition scallee (e : GExpr) : bool := match e with EId _ => true | _ => false end.

(** STRUCTURALLY-supported value expression — the CONSERVATIVE whitelist of [GExpr] forms with NO operand-
    SHAPE hazard: identifiers, integer literals, arithmetic/logical binops, the value-producing unary ops
    (!/^/-), and calls of a function NAME with supported args.  The shape-CONSTRAINED forms are NOT in the
    subset yet — postfix selector/index/slice/type-assertion (each needs its operand to be a struct /
    indexable / sliceable / interface, so [1.f] / [1[0]] / [1[lo:hi]] / [1.(T)] are absurd) and the unary
    deref/addr ([*1] / [&1] are absurd) — so the gate can never certify any of those structural absurdities.
    They re-enter WITH their operand-shape checks when supported.  STRUCTURAL only: it does NOT (and
    syntactically cannot) check SCOPE (an undefined identifier) or TYPES (e.g. [!1], a mismatch) — those are
    the GoSem/type layer.  (The call arg list uses an inline [fix]; [forallb svalue] is guard-opaque, as in
    [gprint]'s arg list.) *)
Fixpoint svalue (e : GExpr) : bool :=
  match e with
  | EId _ => true
  | EInt _ => true
  | EBn _ l r => svalue l && svalue r
  | EUn o e0 => match o with UNot | UXor | UNeg => svalue e0 | UDeref | UAddr => false end
  | ECall callee args =>
      scallee callee &&
      (fix all_ok (l : list GExpr) : bool :=
         match l with nil => true | a :: r => svalue a && all_ok r end) args
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => false
  end.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec (ExpressionStmt) a bare expression
    statement must be a FUNCTION CALL (a plain value like [1] or [a + b] is "evaluated but not used" and
    REJECTED) — AND that call must be a structurally-supported value ([svalue], so [1()] / [x.(int)()] /
    [f(1[0])] are rejected too).  Widens later (receive, specific builtins). *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall _ _ => svalue e
  | _         => false
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
    call-SHAPED but structurally invalid Go; [svalue] rejects it (the callee [EInt 1] is not [scallee]), so
    it is NOT supported and cannot be certified. *)
Definition unsupported_call_value : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EInt 1) nil)].
Example call_value_unsupported : supported_program unsupported_call_value = false.
Proof. reflexivity. Qed.
Fail Example call_value_supported : SupportedProgram unsupported_call_value := eq_refl.

(** REGRESSION (external review 2026-06-28, follow-up²) — a call of a type assertion, `func main(){ x.(int)() }`,
    is call-shaped but a type-assertion callee is not a function NAME, so [scallee] rejects it (the whole
    assertion-callee class is deferred; a concrete [x.(int)] is anyway concretely non-callable). NOT supported. *)
Definition unsupported_assert_call : Program :=
  mkProgram (mkIdent "main" eq_refl)
            [GsExprStmt (ECall (EAssert (EId (mkIdent "x" eq_refl)) GTInt) nil)].
Example assert_call_unsupported : supported_program unsupported_assert_call = false.
Proof. reflexivity. Qed.
Fail Example assert_call_supported : SupportedProgram unsupported_assert_call := eq_refl.

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions value_stmt_unsupported.
