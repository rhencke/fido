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

(** A [GExpr] that is legal as an EXPRESSION STATEMENT in Go.  Per the Go spec (ExpressionStmt) a bare
    expression statement must be a FUNCTION CALL (or a receive op / certain builtins) — a plain value like
    [1] or [a + b] is "evaluated but not used" and REJECTED by the Go compiler.  So [expr_stmt_ok] admits
    ONLY a call for now (it WILL widen: receive, specific builtins).  This is the predicate that keeps
    [SupportedProgram] honest — it never certifies an expression statement Go would reject. *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall _ _ => true
  | _         => false
  end.

(** A statement in the SUPPORTED subset: an expression statement must be [expr_stmt_ok]; a bare [return] is
    always fine (a valid tail of a void func like [main]). *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e => expr_stmt_ok e
  | GsReturn     => true
  end.

(** PHASE-1 supportedness — DECIDABLE (bool-reflected): the program is a runnable `package main` WHOSE BODY is
    entirely in the printer/emitter's supported statement subset.  PURELY SYNTACTIC, but it now means what its
    name says: a [SupportedProgram] is one the blessed emitter prints as VALID Go.  Crucially it does NOT
    certify a bare-value statement like `func main(){ 1 }` (Go rejects "evaluated but not used"):
    [supported_program] is [false] there, so NO certificate exists and [emit_supported] can never print it.
    The package-name-only check was too weak (it certified invalid Go) — fixed.  This is SUPPORTEDNESS, not a
    behavioral-safety claim — that is [BehaviorSafe] (below, once GoSem exists). *)
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

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions value_stmt_unsupported.
