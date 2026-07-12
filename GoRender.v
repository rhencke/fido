(** ============================================================================
    GoRender — the DIRECT pretty-printer: it traverses a decorated [CompiledFile] and
    emits Go source bytes.  There is NO tokenizer, token encoder, lexer, parser, text IR,
    or AST→text→AST round trip — the renderer is a direct [CompiledFile -> string] function,
    and its correctness (next module tick) is STRUCTURAL over the intrinsically-grammatical
    compiled tree, never "a parser recovers the same AST" (doc §4; PAINFUL_LESSONS #3).

    It renders the RESOLVED tree: a [CBool] prints its predeclared spelling, the callee is
    the literal builtin [println], and package/function are the pinned "main" constants —
    the renderer never resolves names, infers types, validates, or repairs (GoCompile did
    all of that).  Its only decisions are serialization inherent to Go syntax: legal literal
    spelling/escaping, canonical spacing/newlines, deterministic layout.  There are no binary
    operators in this fragment, so no precedence or parenthesis decision arises and there is
    no parenthesis node.

    Lexical fusion is prevented by direct canonical spacing (a space after [package]/[func],
    a comma-space between arguments) — not a token framework.  Decimal digits come from the
    one authority ([digits.print_Z]); a [CInt]/[CNeg] magnitude is [N], rendered via [Z.of_N]
    (nonnegative, so no sign — [CNeg]'s sign is the explicit leading [-]).
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List.
From Fido Require Import digits Literals GoAST GoCompile.
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
    (printable ASCII + tab + newline) can require; every other admitted char is verbatim. *)
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

(** ---- The renderer over the decorated tree ---- *)

Definition render_cexpr (c : CompiledExpr) : string :=
  match c with
  | CBool true  => "true"
  | CBool false => "false"
  | CInt n _ => print_Z (Z.of_N n)
  | CNeg n _ => "-" ++ print_Z (Z.of_N n)
  | CStr s _ => quote ++ escape_string s ++ quote
  end.

Fixpoint render_cargs (cs : list CompiledExpr) : string :=
  match cs with
  | []        => ""
  | [c]       => render_cexpr c
  | c :: cs'  => render_cexpr c ++ ", " ++ render_cargs cs'
  end.

Definition render_cstmt (s : CompiledStmt) : string :=
  match s with
  | CPrintln args => tab ++ "println(" ++ render_cargs args ++ ")" ++ nl
  end.

Fixpoint render_cstmts (ss : list CompiledStmt) : string :=
  match ss with
  | []       => ""
  | s :: ss' => render_cstmt s ++ render_cstmts ss'
  end.

(** Package and function are the pinned "main" constants (a [CompiledFile] cannot be
    otherwise), so they are emitted literally. *)
Definition render_cfile (c : CompiledFile) : string :=
  "package main" ++ nl ++ nl
  ++ "func main() {" ++ nl
  ++ render_cstmts (cf_body c)
  ++ "}" ++ nl.
