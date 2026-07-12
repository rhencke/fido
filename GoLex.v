(** ============================================================================
    GoLex — the Go lexer for the checkpoint-66 slice: bytes -> post-ASI token stream.

    Faithful to Go's lexical rules on this subset: [package]/[func] keywords, identifiers
    ([true]/[false] are identifiers), NONNEGATIVE decimal integer literals (a leading zero
    followed by a digit is rejected — that is Go's octal form, out of this slice),
    interpreted string literals with exactly the four escapes backslash-quote,
    backslash-backslash, backslash-n, backslash-t (a raw newline inside a literal is
    illegal), the punctuation [( ) { } , -], and AUTOMATIC
    SEMICOLON INSERTION at a line end whose last token is an identifier, a literal, [)]
    or [}] (GoToken.[asi_after]).

    ONE structural fixpoint over the input string — every recursive call peels one
    character (no fuel, no well-founded wrapper); the mode carries the in-progress
    lexeme, and [last] carries the previous significant token for ASI.  Used by the
    render/lex inverse theorems and by nothing load-bearing at run time.
    ============================================================================ *)
From Stdlib Require Import String Ascii ZArith Bool List.
From Fido Require Import GoToken.
Import ListNotations.
Open Scope string_scope.

Definition is_space  (c : ascii) : bool :=
  (Nat.eqb (nat_of_ascii c) 32) || (Nat.eqb (nat_of_ascii c) 9).
Definition is_nl     (c : ascii) : bool := Nat.eqb (nat_of_ascii c) 10.
Definition is_digit  (c : ascii) : bool :=
  (Nat.leb 48 (nat_of_ascii c)) && (Nat.leb (nat_of_ascii c) 57).
Definition is_letter (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) || ((Nat.leb 97 n) && (Nat.leb n 122)) || (Nat.eqb n 95).
Definition is_idchar (c : ascii) : bool := is_letter c || is_digit c.
Definition digit_val (c : ascii) : Z := Z.of_nat (nat_of_ascii c - 48).

Definition quote_c : ascii := ascii_of_nat 34.
Definition bslash_c : ascii := ascii_of_nat 92.
Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.

(** The subset's single-character punctuation tokens. *)
Definition punct_token (c : ascii) : option GoToken :=
  if Ascii.eqb c "(" then Some TLParen
  else if Ascii.eqb c ")" then Some TRParen
  else if Ascii.eqb c "{" then Some TLBrace
  else if Ascii.eqb c "}" then Some TRBrace
  else if Ascii.eqb c "," then Some TComma
  else if Ascii.eqb c "-" then Some TMinus
  else None.

(** Escape decoding inside an interpreted string literal (exactly the admitted four). *)
Definition unescape (c : ascii) : option ascii :=
  if Ascii.eqb c "n" then Some nl_c
  else if Ascii.eqb c "t" then Some tab_c
  else if Ascii.eqb c quote_c then Some quote_c
  else if Ascii.eqb c bslash_c then Some bslash_c
  else None.

Inductive LexMode : Type :=
| MStart
| MWord   : string -> LexMode          (* identifier/keyword lexeme so far *)
| MNum    : Z -> bool -> LexMode       (* value so far; flag: lexeme is exactly "0" *)
| MStr    : string -> LexMode          (* string payload (unescaped) so far *)
| MStrEsc : string -> LexMode.         (* just saw a backslash inside a literal *)

Definition opt_cons (t : GoToken) (r : option (list GoToken)) : option (list GoToken) :=
  match r with Some ts => Some (t :: ts) | None => None end.

Fixpoint lex_steps (mode : LexMode) (last : option GoToken) (s : string)
  : option (list GoToken) :=
  match s with
  | EmptyString =>
      match mode with
      | MStart     => Some []
      | MWord acc  => Some [classify_word acc]
      | MNum v _   => Some [TIntLit v]
      | MStr _ | MStrEsc _ => None                     (* unterminated string literal *)
      end
  | String c s' =>
      match mode with
      | MStart =>
          if is_space c then lex_steps MStart last s'
          else if is_nl c then
            match last with
            | Some t => if asi_after t
                        then opt_cons TSemi (lex_steps MStart (Some TSemi) s')
                        else lex_steps MStart last s'
            | None => lex_steps MStart last s'
            end
          else if is_letter c then lex_steps (MWord (String c EmptyString)) last s'
          else if is_digit c then lex_steps (MNum (digit_val c) (Z.eqb (digit_val c) 0)) last s'
          else if Ascii.eqb c quote_c then lex_steps (MStr EmptyString) last s'
          else match punct_token c with
               | Some t => opt_cons t (lex_steps MStart (Some t) s')
               | None => None
               end
      | MWord acc =>
          if is_idchar c then lex_steps (MWord (acc ++ String c EmptyString)) last s'
          else let t := classify_word acc in
          if is_space c then opt_cons t (lex_steps MStart (Some t) s')
          else if is_nl c then
            (if asi_after t
             then opt_cons t (opt_cons TSemi (lex_steps MStart (Some TSemi) s'))
             else opt_cons t (lex_steps MStart (Some t) s'))
          else if Ascii.eqb c quote_c then opt_cons t (lex_steps (MStr EmptyString) (Some t) s')
          else match punct_token c with
               | Some p => opt_cons t (opt_cons p (lex_steps MStart (Some p) s'))
               | None => None
               end
      | MNum v z =>
          if is_digit c then
            (if z then None                            (* "0<digit>" — octal form, out of slice *)
             else lex_steps (MNum (v * 10 + digit_val c) false) last s')
          else if is_letter c then                     (* "42x": literal then adjacent identifier *)
            opt_cons (TIntLit v) (lex_steps (MWord (String c EmptyString)) (Some (TIntLit v)) s')
          else let t := TIntLit v in
          if is_space c then opt_cons t (lex_steps MStart (Some t) s')
          else if is_nl c then
            opt_cons t (opt_cons TSemi (lex_steps MStart (Some TSemi) s'))  (* asi_after (TIntLit _) = true *)
          else if Ascii.eqb c quote_c then opt_cons t (lex_steps (MStr EmptyString) (Some t) s')
          else match punct_token c with
               | Some p => opt_cons t (opt_cons p (lex_steps MStart (Some p) s'))
               | None => None
               end
      | MStr acc =>
          if Ascii.eqb c quote_c then
            opt_cons (TStrLit acc) (lex_steps MStart (Some (TStrLit acc)) s')
          else if Ascii.eqb c bslash_c then lex_steps (MStrEsc acc) last s'
          else if is_nl c then None                    (* raw newline in an interpreted literal *)
          else lex_steps (MStr (acc ++ String c EmptyString)) last s'
      | MStrEsc acc =>
          match unescape c with
          | Some u => lex_steps (MStr (acc ++ String u EmptyString)) last s'
          | None => None
          end
      end
  end.

Definition lex (s : string) : option (list GoToken) := lex_steps MStart None s.
