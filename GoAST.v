(** ============================================================================
    GoAST — the ONE raw program representation.  The permanent root is a PROGRAM, not a file:

      GoProgram := fmap GoFileAST        (a verified finite map: unique relative path -> raw file AST)

    A [GoFileAST] is the raw syntax proposed for ONE file — nothing compiled.  Package grouping,
    package identifiers, imports, entry point, resolved symbols/types/calls, and the package graph are
    COMPILATION RESULTS derived by GoCompile over the whole path-indexed program; they are NOT baked
    into the raw file value, and there is no raw GoPackage hierarchy.

    The current admitted fragment is deliberately tiny: a file is structurally a [MainFile] (package
    main + func main STRUCTURAL — the MVP constructor "is a main-package file"; no identifiers, no
    imports, no other file shapes yet), whose body is [SPrintln] statements (the builtin println is
    the statement, not a callee name) over primitive literals: bool ([EBool]) and integers as an
    unsigned magnitude ([EInt]) or its negation ([ENeg]).  Anything else is UNREPRESENTABLE.  The MVP
    is exactly one program -> one main package -> one file, expressed as a proved subset over this
    general finite-map program structure — never by making a single file the root.
    ============================================================================ *)
From Stdlib Require Import NArith List String.
From Fido Require Import FMap.

Inductive GoExpr : Type :=
| EBool : bool -> GoExpr
| EInt  : N -> GoExpr
| ENeg  : N -> GoExpr.

Inductive GoStmt : Type :=
| SPrintln : list GoExpr -> GoStmt.

(** The raw AST of one source file (currently only the main-file shape). *)
Inductive GoFileAST : Type :=
| MainFile : list GoStmt -> GoFileAST.

Definition RelativePath := string.

(** The raw program: a finite map from unique relative paths to raw file ASTs. *)
Definition GoProgram := fmap GoFileAST.
