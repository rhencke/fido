(** ============================================================================
    GoToken — the Go token universe for the checkpoint-66 slice (post-ASI logical
    stream: [TSemi] is the statement terminator, whether written or inserted).

    This module is consumed by BOTH the independent grammar (GoGrammar) and the
    lexer/renderer (GoLex/GoRender); it contains no policy of either.  [true]/[false]
    are PREDECLARED IDENTIFIERS in Go, not keywords — they lex as [TIdent], exactly as
    Go's lexer classifies them; only [package]/[func] are keywords in this subset.
    ============================================================================ *)
From Stdlib Require Import String ZArith.

Inductive GoToken : Type :=
| KwPackage | KwFunc
| TIdent  : string -> GoToken
| TIntLit : Z -> GoToken        (* a DECIMAL integer literal: nonnegative by construction of the lexer/renderer *)
| TStrLit : string -> GoToken   (* an interpreted string literal; the PAYLOAD (unescaped) — source escaping is lexical *)
| TLParen | TRParen | TLBrace | TRBrace
| TComma | TMinus
| TSemi.                        (* statement terminator (explicit or ASI-inserted) *)

(** Go's automatic-semicolon rule, restricted to this token subset: a semicolon is
    inserted at a line end when the line's final token is an identifier, an integer or
    string literal, or one of [)] [}].  (The full Go rule also names other literal kinds,
    [break]/[continue]/[fallthrough]/[return], [++]/[--], and []]  — none exist in this
    subset.) *)
Definition asi_after (t : GoToken) : bool :=
  match t with
  | TIdent _ | TIntLit _ | TStrLit _ | TRParen | TRBrace => true
  | _ => false
  end.

(** Keyword classification for a completed word lexeme (the subset's two keywords). *)
Definition classify_word (w : string) : GoToken :=
  if String.eqb w "package" then KwPackage
  else if String.eqb w "func" then KwFunc
  else TIdent w.
