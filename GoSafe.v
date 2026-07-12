(** ============================================================================
    GoSafe — the exact ABSTRACT println-trace semantics of the admitted fragment, and [SafeProgram], the
    permanent safety capability boundary over a [CompilableProgram].

    This is NOT a full Go operational semantics — it is a deterministic abstract-trace mapping for the
    current tiny fragment: values are REAL Go values ([VBool]/[VInt : Z], not source spelling — so
    [EInt 0] and [ENeg 0] evaluate equal), and a file's behaviour is the ordered sequence of its
    [println] calls (each the list of its argument VALUES).  There is no panic/blocking/scheduler/heap
    algebra: no admitted operation can panic or diverge, so predeclaring one would be scaffolding.

    [SafeProgram] is the PERMANENT home for guarantees BEYOND compiler acceptance (nil-deref / bounds /
    panic-freedom / happens-before / race- or deadlock-freedom subsets / termination / protocol
    invariants / user- or LLM-added refinements).  [GoSafe cp := True] is honest TODAY only because every
    [CompilableProgram] representable in this fragment satisfies the current safety floor — NOT by
    circular reference to compilation.  Stronger proofs REFINE it over the same [CompilableProgram];
    they never fork the compiler, AST, renderer, or semantics.
    ============================================================================ *)
From Stdlib Require Import ZArith List String.
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

(** By VALUE, not spelling: a zero literal and a negated zero agree. *)
Lemma eval_zero_sign_agnostic : eval_expr (EInt 0) = eval_expr (ENeg 0).
Proof. reflexivity. Qed.

Definition eval_stmt (s : GoStmt) : list GoValue :=
  match s with SPrintln args => map eval_expr args end.

Definition eval_decl (d : GoDecl) : list (list GoValue) :=
  match d with DMain body => map eval_stmt body end.

(** A file's exact abstract behaviour: the println calls of its declarations, in program order. *)
Definition eval_file (f : GoFileAST) : list (list GoValue) := flat_map eval_decl f.

(** ---- the safety certificate ---- *)

(** Trivial TODAY (the fragment has no unsafe operation), kept as the permanent extension point. *)
Definition GoSafe (cp : CompilableProgram) : Prop := True.

Record SafeProgram : Type := mkSafe {
  sp_compiled : CompilableProgram;
  sp_safe     : GoSafe sp_compiled
}.

(** A compilation certificate suffices for the current fragment; [sp_compiled] carries the genuine
    whole-program compile proof, so nothing uncompilable is certified. *)
Definition certify (cp : CompilableProgram) : SafeProgram := mkSafe cp I.

(** The certified program (what the public renderer/emitter traverse — only through SafeProgram). *)
Definition sp_program (sp : SafeProgram) : GoProgram := cp_program (sp_compiled sp).

(** The compiler-derived package name the renderer emits for this program's files. *)
Definition sp_pkg_name (sp : SafeProgram) : string := cf_pkg_name (cp_facts (sp_compiled sp)).
