
(* ── §15 Rendering: contexts, exact equations, real whitespace properties ──── *)
Inductive RenderContext : Type :=
| TopContext | UnaryOperandContext | ApplicationHeadContext | ApplicationArgumentContext.

(* Canonical grouping is decided by the spec count: exactly one renders ungrouped, zero or two-or-more
   render grouped.  Pinned `gc` accepts the empty group, so both forms are reachable. *)
Definition renders_grouped {A : Type} (specs : list A) : bool :=
  match specs with [_] => false | _ => true end.

Parameter needs_parens : RenderContext -> Expr -> bool.
Parameter render_in : RenderContext -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_literal : Literal -> string.
(* The three literal emission authorities: canonical decimal for magnitudes, canonical Go escaping for
   strings.  Nothing else may spell a literal. *)
Parameter decimal_of_magnitude : N -> string.
Parameter decimal_of_float : NonNegativeDecimal -> string.
Parameter escape_go_string : string -> string.
Parameter render_type_expr : TypeExpr -> string.
Parameter render_binding_name : BindingName -> string.
(* §16 Depth-aware rendering: a grouped local declaration has internal newlines and cannot be correctly
   indented by prepending one tab to the finished string.  These are the permanent structural roots. *)
Parameter render_declaration_at : nat -> Declaration -> string.
Parameter render_stmt_at : nat -> Stmt -> string.
Parameter render_block_at : nat -> Block -> string.
Parameter render_top_decl : TopLevelDecl -> string.

Definition render_declaration : Declaration -> string := render_declaration_at 0.
Definition render_stmt : Stmt -> string := render_stmt_at 0.
Definition render_block : Block -> string := render_block_at 0.
Parameter render_file : SyntaxFile -> string.
Parameter render_const_spec : ConstSpec -> string.
Parameter render_var_spec : VarSpec -> string.
Parameter render_type_spec : TypeSpec -> string.
Parameter render_program : SyntaxProgram -> list (string * string).
Parameter render_gomod : ModuleSpec -> string.

Fixpoint InString (c : ascii) (s : string) : Prop :=
  match s with EmptyString => False | String c' rest => c = c' \/ InString c rest end.

Definition first_char (s : string) : option ascii :=
  match s with EmptyString => None | String c _ => Some c end.

Fixpoint last_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c EmptyString => Some c
  | String _ rest => last_char rest
  end.

(* Exactly two adjacent bytes: a token-boundary property, not a scan of arbitrary contents. *)
Fixpoint HasAdjacent (a b : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c rest => (c = a /\ first_char rest = Some b) \/ HasAdjacent a b rest
  end.

Definition NewlineChar : ascii := ascii_of_nat 10.
Definition SpaceChar : ascii := ascii_of_nat 32.
Definition TabChar : ascii := ascii_of_nat 9.

Definition StartsWithMinus (s : string) : Prop := first_char s = Some "-"%char.
Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.

(* No line ends in a space or a tab, and the final byte is a newline. *)
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasAdjacent SpaceChar NewlineChar s /\
  ~ HasAdjacent TabChar NewlineChar s /\
  last_char s = Some NewlineChar.
