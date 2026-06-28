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
From Stdlib Require Import String.
Open Scope string_scope.

(** PHASE-1 supportedness: the program is a runnable `package main`.  PURELY SYNTACTIC (a property of the
    package name) — provable by [reflexivity] for a well-formed program — so the blessed emitter only ever
    prints a runnable main package; a non-main package cannot be certified.  Deliberately tiny: it WILL widen
    (supported decls / statements / types) as the AST grows.  This is supportedness, NOT a behavioral-safety
    claim — that is [BehaviorSafe] (below, once GoSem exists). *)
Definition SupportedProgram (p : Program) : Prop := proj1_sig (prog_pkg p) = "main".

(** Reserved for the GoSem era: behavioral safety over the AST's denotation.  Stated only as the eventual
    shape; NOT yet defined, because there is no authoritative GoSem to define it against — and a placeholder
    [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the charter forbids
    (§8 Rule 4).  When GoSem lands: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its
    GoSem denotation>], and GoEmit gains [SafeProgram]/[emit_safe]. *)
