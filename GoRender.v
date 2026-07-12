(** ============================================================================
    GoRender — the DIRECT precedence-aware pretty-printer: it traverses a [GoFile] and
    emits Go source bytes.  There is NO tokenizer, token encoder, lexer, parser, text IR,
    or AST→text→AST round trip — the renderer is a direct [GoAST -> string] function, and
    its correctness is structural, never "a parser recovers the same AST".

    The renderer only makes serialization decisions inherent to Go syntax: operator
    precedence/associativity and required-vs-omitted parentheses (TRIVIAL in this fragment —
    there are no binary operators yet, so no parenthesis ever needs emitting, and there is
    no parenthesis AST node), legal literal spelling/escaping, canonical spacing/newlines,
    and deterministic layout.  It never resolves names, infers types, validates, or repairs
    — it receives a settled [GoFile] (emission is gated on GoSafe) and serializes it.

    Lexical fusion is handled by direct canonical spacing (a space after [package]/[func]
    and after each [,]) — no general token/separator framework.  In this fragment the only
    adjacency of two word lexemes is keyword|identifier, always separated by the template's
    space.  Decimal digits come from the one authority (digits.[print_Z]); an [EInt]/[ENeg]
    magnitude is [N], rendered via [Z.of_N] (nonnegative, so no sign — the sign of [ENeg] is
    the explicit leading [-]).
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List.
From Fido Require Import digits Literals GoIdent GoAST.
Import ListNotations.
Open Scope string_scope.

Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.
Definition quote_c : ascii := ascii_of_nat 34.
Definition bslash_c : ascii := ascii_of_nat 92.
Definition nl : string := String nl_c EmptyString.
Definition tab : string := String tab_c EmptyString.
Definition quote : string := String quote_c EmptyString.
Definition bslash : string := String bslash_c EmptyString.

(** Source escaping of a string payload — exactly the four escapes the admitted charset
    can require; every other admitted char (printable ASCII) is verbatim. *)
Definition escape_char (c : ascii) : string :=
  if Ascii.eqb c quote_c then bslash ++ quote
  else if Ascii.eqb c bslash_c then bslash ++ bslash
  else if Ascii.eqb c nl_c then bslash ++ "n"
  else if Ascii.eqb c tab_c then bslash ++ "t"
  else String c EmptyString.

Fixpoint escape_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_char c ++ escape_string s'
  end.

Definition render_expr (e : GoExpr) : string :=
  match e with
  | EIdent i => ident_str i
  | EInt n   => print_Z (Z.of_N n)
  | ENeg n   => "-" ++ print_Z (Z.of_N n)
  | EStr s _ => quote ++ escape_string s ++ quote
  end.

Fixpoint render_args (es : list GoExpr) : string :=
  match es with
  | []       => ""
  | [e]      => render_expr e
  | e :: es' => render_expr e ++ ", " ++ render_args es'
  end.

Definition render_stmt (s : GoStmt) : string :=
  match s with
  | SCall callee args => tab ++ ident_str callee ++ "(" ++ render_args args ++ ")" ++ nl
  end.

Fixpoint render_stmts (ss : list GoStmt) : string :=
  match ss with
  | []       => ""
  | s :: ss' => render_stmt s ++ render_stmts ss'
  end.

Definition render_file (f : GoFile) : string :=
  "package " ++ ident_str (file_pkg f) ++ nl ++ nl
  ++ "func " ++ ident_str (fn_name (file_func f)) ++ "() {" ++ nl
  ++ render_stmts (fn_body (file_func f))
  ++ "}" ++ nl.
