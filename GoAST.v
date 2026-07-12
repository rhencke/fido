(** ============================================================================
    GoAST — the ONE program representation.  Everything the current slice does NOT model
    exactly is STRUCTURAL, not an identifier the compiler could reject: the program is a
    [MainFile] (package [main] + one [func main()] are the datatype, not names), whose body
    is a list of [SPrintln] (the builtin [println] is the statement, not a callee identifier),
    whose arguments are the exact admitted primitives.  There is no package/function/call/
    expression identifier — those Go features are UNREPRESENTABLE until their full compiler
    behaviour is modelled, so a non-[main] package or a [print] call is not "rejected as
    invalid Go", it simply cannot be proposed.

    [GoCompile] adds only the remaining static obligation (integer representability) over this
    SAME tree; there is no second "compiled" syntax hierarchy, no erasure.

    Admitted primitives: booleans, and integers as an UNSIGNED magnitude ([EInt]) or its unary
    negation ([ENeg]) — Go has no signed integer literal.  (Strings are deferred until their
    independent literal-denotation proofs exist.)
    ============================================================================ *)
From Stdlib Require Import NArith List.

Inductive GoExpr : Type :=
| EBool : bool -> GoExpr        (* the predeclared [true]/[false] *)
| EInt  : N -> GoExpr           (* unsigned decimal magnitude *)
| ENeg  : N -> GoExpr.          (* unary minus over a magnitude; denotes -[N] *)

Inductive GoStmt : Type :=
| SPrintln : list GoExpr -> GoStmt.   (* the builtin println is the statement, not a callee name *)

Inductive GoFile : Type :=
| MainFile : list GoStmt -> GoFile.   (* package main + func main() are structural *)
