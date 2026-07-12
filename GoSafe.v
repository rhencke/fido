(** ============================================================================
    GoSafe — the exact operational semantics of the admitted fragment, and the safety
    certificate over a [CompiledProgram].

    Values are REAL Go values, not source spelling: a printed integer is a signed [Z], so a
    literal and its negation observe the same value when they denote the same integer — in
    particular [EInt 0] and [ENeg 0] both evaluate to [VInt 0] ([eval_zero_sign_agnostic]).
    (This is the accurate foundation user/LLM theorems layer over: they must not be able to
    "prove" a distinction the target program does not make.)

    [run] is the exact print-event behaviour: the ordered sequence of [println] calls, each the
    list of its argument VALUES.  It is a total function (evaluation terminates by structure),
    and the admitted operations (println of primitive literals) have NO panic, division,
    indexing, nil-deref, blocking, or nontermination source — so there is no [Panicked]/
    [Outcome] algebra here (that would be future scaffolding for constructors that do not yet
    exist).  [GoSafe] is therefore the honest, currently-trivial universal obligation over this
    fragment; it gains real premises the moment a partial/unsafe constructor is added — at which
    point the exact distinction is introduced together with that constructor, not predeclared.
    ============================================================================ *)
From Stdlib Require Import ZArith List.
From Fido Require Import GoAST GoCompile.
Import ListNotations.

Inductive GoValue : Type :=
| VBool : bool -> GoValue
| VInt  : Z -> GoValue.

Definition eval_expr (e : GoExpr) : GoValue :=
  match e with
  | EBool b => VBool b
  | EInt n  => VInt (Z.of_N n)
  | ENeg n  => VInt (Z.opp (Z.of_N n))
  end.

(** The exact value semantics is by VALUE: a zero literal and a negated zero agree. *)
Lemma eval_zero_sign_agnostic : eval_expr (EInt 0) = eval_expr (ENeg 0).
Proof. reflexivity. Qed.

Definition eval_stmt (s : GoStmt) : list GoValue :=
  match s with SPrintln args => map eval_expr args end.

(** The observable behaviour: one entry per println call, in program order. *)
Definition run (f : GoFile) : list (list GoValue) :=
  match f with MainFile body => map eval_stmt body end.

(** ---- the safety certificate ---- *)

(** The universal safety obligation over the admitted fragment.  It is currently trivial BY
    CONSTRUCTION (no admitted operation can panic, block, or diverge — [run] is total and
    effect-only) — NOT by circular reference to compilation.  A real premise appears here when
    the first partial/unsafe constructor enters. *)
Definition GoSafe (cp : CompiledProgram) : Prop := True.

Record SafeProgram : Type := mkSafe {
  sp_cp   : CompiledProgram;
  sp_safe : GoSafe sp_cp
}.

(** Build a certificate from a compilation (the fragment's safety obligation is discharged by
    construction; [sp_cp] carries the genuine compile proof, so nothing uncompilable is
    certified). *)
Definition certify (cp : CompiledProgram) : SafeProgram := mkSafe cp I.

(** The certified program's AST (what the renderer/emitter consume). *)
Definition sp_ast (sp : SafeProgram) : GoFile := cp_ast (sp_cp sp).
