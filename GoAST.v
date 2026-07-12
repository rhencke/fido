(** ============================================================================
    GoAST — the ONE program representation: a raw, LLM-proposed Go tree.  There is no
    separate surface/typed/target IR — this AST *is* the IR; "compiled" and "safe" are
    PROOFS about a [GoFile] (GoCompile / GoSafe), not new trees.

    A [GoFile] may be compiler-INVALID (an unresolved identifier, an out-of-range integer,
    a wrong package name) — that is intentional: it is where an untrusted proposer writes a
    program, which GoCompile then accepts or rejects.  But it may NOT contain syntax whose
    compiler rules are not modeled exactly: unsupported forms are absent from the datatype,
    never admitted with a "known narrowing".  Lexical well-formedness is structural
    (identifiers are validated [GoIdent]s; an integer literal is an UNSIGNED magnitude [N] —
    a negative value is [ENeg], unary minus over a magnitude, never a signed literal token;
    a string carries its admitted-charset evidence).  There is NO parenthesis node — the
    tree is the operation tree, and parentheses appear only in the rendered bytes when Go
    precedence requires them to preserve that tree.
    ============================================================================ *)
From Stdlib Require Import String NArith List.
From Fido Require Import Literals GoIdent.
Import ListNotations.

Inductive GoExpr : Type :=
| EIdent : GoIdent -> GoExpr                       (* any validated identifier; resolution is GoCompile's job *)
| EInt   : N -> GoExpr                             (* unsigned decimal magnitude *)
| ENeg   : N -> GoExpr                             (* unary minus over a magnitude; denotes -[N] *)
| EStr   : forall s : string, str_ok s = true -> GoExpr.

Inductive GoStmt : Type :=
| SCall : GoIdent -> list GoExpr -> GoStmt.        (* callee(args) as an expression statement *)

Record GoFunc : Type := mkGoFunc {
  fn_name : GoIdent;
  fn_body : list GoStmt
}.

Record GoFile : Type := mkGoFile {
  file_pkg  : GoIdent;
  file_func : GoFunc
}.
