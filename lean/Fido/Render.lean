-- Port of Render.v (lean/README.md).
import Fido.Decimal
import Fido.Float
import Fido.Complex
import Fido.ModulePath
import Fido.Version
import Fido.Names
import Fido.Syntax

/-! divergences:
  * THE BYTE BOUND (README: `ascii` is `Char`; "where a proof relied on `< 256`, the bound is stated").
    Rocq's `ascii` is exactly the 256 bytes; `Char` holds every Unicode scalar, so a `Str` — and a
    `Syntax.StringLiteral` — can hold characters no Rocq string can.  On such a character `string_byte` /
    `hex_escape` do not describe a byte: `hex_digit (c.toNat / 16)` is `Char.ofNat (87 + c.toNat / 16)`,
    which for `c.toNat ≥ 656` is not ASCII and for `c.toNat ≥ 256` is not a hex digit.  So the `.v`'s
    unconditional statements over a SOURCE string or an AST containing one are FALSE as literally
    restated over `Char`, and the port states the bound on exactly those and nothing else:
      - `nat_of_ascii_lt_256` (the bound itself) takes `c.toNat < 256` and is degenerate;
      - `hex_escape_ascii`, `string_byte_ascii`, `hex_escape_exact`, `decode_render_byte` take
        `c.toNat < 256`; `string_body_ascii`, `string_literal_ascii`, `decode_body_render`,
        `string_roundtrip` take `∀ c ∈ s, c.toNat < 256`;
      - the AST-level ASCII lemmas (`render_literal_ascii`, `render_expr_ascii`, `render_args_ascii`,
        `render_ne_exprs_ascii`, `render_const_spec_ascii`, `render_var_spec_ascii`,
        `render_declaration_ascii`, `render_stmt_ascii`, `render_stmts_ascii`, `render_block_ascii`,
        `render_top_level_decl_ascii`, `render_top_levels_ascii`, `file_ascii`) take the corresponding
        `*_bytes` predicate — ten `Prop`-valued definitions with no `.v` counterpart
        (`literal_bytes` … `file_bytes`), each saying "every string literal inside is a byte string".
        Emit.v consumes `Render.file_ascii` unconditionally, so this bound will reach Emit's port.
    Every other statement is unchanged: the no-newline lemmas (`hex_escape_no_nl_cr`, `string_byte_no_nl_cr`,
    `string_body_no_nl_cr`, `string_literal_no_nl_cr`) and `byte_reconstruct` are TRUE for every `Char`
    (`Char.ofNat n` is `n` or `0`, never 10 or 13, for `n ≥ 48`; `Char.ofNat c.toNat = c` always) and are
    proved so, although their `.v` proofs went through the bound.  `render_args_ascii_of`,
    `render_spec_lines_ascii` and `render_group_ascii` keep their exact conditional statements; the last two
    are derived from private membership-restricted forms (`∀ s ∈ specs, …`), which the bounded
    `render_declaration_ascii` needs.
  * `ascii_of_nat n` is `Char.ofNat n` (every byte is a valid scalar; Decimal.lean's `digit` wraps modulo 256
    for its own reason); `nat_of_ascii c` is `c.toNat`; `Ascii.eqb` is `==` (`decide (_ = _)`), `Nat.eqb` /
    `Nat.leb` / `Nat.ltb` / `Z.eqb` / `Z.ltb` / `String.eqb` are `decide` on the propositions; Rocq's `if` on
    a `bool` is `bif`; `String c s` is `c :: s`, literals are `str! "…"`, `EmptyString` is `[]`, `++` is
    list append (Lean's is left-associative, Rocq's right; the statements are written in Lean's association).
    `Z.of_N n` is `(n : Int)` (Syntax.lean: `N` is `Nat`), `Z.opp` is `-`, `option_map` is `Option.map`,
    `String c` as a function is `(c :: ·)`.
  * `positive` is `Nat` with `0 < p` carried (README): `positive_ascii`, `positive_digit_value`,
    `positive_no_leading_zero`, `positive_head_not_minus` and `str_all_digits_print_Z_pos` take `0 < p`, and
    `Z` cases are `.ofNat 0` / `.ofNat (n + 1)` / `.negSucc n` (Decimal.lean).  Rocq's `exists_last` is
    core's `List.eq_nil_or_concat`; `Forall`/`In` are `∀ x ∈ l, P x`/`∈`; `fold_left_app` is a private
    `foldl_append` (core's carries `propext` and `Quot.sound`).
  * `render_expr` cannot recurse through the higher-order `render_arglist render_expr args` (Lean's structural
    recursion does not see through it), so `render_expr` and `render_args` are one `mutual` structural
    definition over the nested `Expr`/`List Expr`; `render_arglist` keeps its generic `.v` definition and the
    private `render_args_arglist` records the `.v`'s `render_args es := render_arglist render_expr es`.
    `render_app` is still `rfl`.
  * Catch-all `_` match arms are enumerated (README): `expr_is_unary`, `render_names`, `render_group`,
    `decode_string_body`, `decode_decimal_body`, `go_int_lit`, `read_go_int`.
  * `Opaque hex_digit decode_hex_digit` / `Transparent` have no counterpart: `decode_hex_prefix` goes through
    a private `decode_hex_case` (`rfl`), and the five one-letter escapes of `decode_render_byte` through a
    private `decode_simple_escape` — `decode_string_body` applied to a cons with a variable tail does not
    unfold under `rfl` (the unifier stalls on the recursive call), so that one rewrites with the proven
    `decode_string_body.eq_def` (its per-arm equation lemmas are split by the nested matches).
    `Example`s are `theorem`s; the five render examples that print a positive go through
    `Decimal.positive_digits` (well-founded) and use `decide +kernel` (`repair_bare_render`, 2^63: 0.25 s of
    kernel type checking; Rocq's `reflexivity` was structural).
  * Axiom closure (the audit's finding; no statement changes): every constant that mentions `Decimal.integer`
    or `Decimal.positive` — the renderer from `render_literal` up, `file`, `positive_ascii` … `file_ascii`,
    the faithfulness, `read_*` and `go_int_lit_*_literal` lemmas and the seven render examples — inherits
    `propext` and `Quot.sound` from Decimal.lean's well-founded `positive_digits` (`WellFounded.fix`);
    `hex_escape_ascii` … `string_literal_ascii` carry `propext` through `Nat.div_lt_iff_lt_mul`, and
    `byte_reconstruct` … `string_roundtrip` both axioms through it and `Nat.div_add_mod`; `omega` (Rocq:
    `lia`) is the sole source only in `digits_dval`.  Axiom-free: `str_ascii_app` … `integer_ascii`'s
    digit lemmas, the identifier / binding / type / names / spec-line / group renders, everything about
    `module_file`, the whole no-newline chain, the decoder shape lemmas (`hex_digit_decode`,
    `decode_hex_prefix`, `read_nat_all_digits`, `read_signed_dec_all_digits`, `read_signed_dec_sign`,
    `char_digit_not`, `go_int_lit_all_digits_nonempty`, `go_int_lit_neg`) and the eleven byte examples.
    Nothing here reaches `Classical.choice`. -/

namespace Fido.Render
open Fido.Syntax (Expr)
open Fido.Syntax.Expr

def nl_c : Char := Char.ofNat 10
def tab_c : Char := Char.ofNat 9
def nl : Str := [nl_c]
def tab : Str := [tab_c]

/-- The exact first line of every generated file; note the two spaces after the period. -/
def header : Str := str! "// fido was here.  woof woof.  do not edit."

/-! The canonical Go interpreted string literal: one spelling per semantic byte sequence. -/

def cr_c     : Char := Char.ofNat 13
def dquote_c : Char := Char.ofNat 34   -- the double-quote byte 0x22
def bslash_c : Char := Char.ofNat 92

def hex_digit (k : Nat) : Char :=
  bif decide (k < 10) then Char.ofNat (48 + k) else Char.ofNat (87 + k)

def hex_escape (c : Char) : Str :=
  let n := c.toNat
  bslash_c :: 'x' :: hex_digit (n / 16) :: hex_digit (n % 16) :: []

def string_byte (c : Char) : Str :=
  let n := c.toNat
  bif decide (n = 34) then bslash_c :: dquote_c :: []
  else bif decide (n = 92) then bslash_c :: bslash_c :: []
  else bif decide (n = 10) then bslash_c :: 'n' :: []
  else bif decide (n = 9)  then bslash_c :: 't' :: []
  else bif decide (n = 13) then bslash_c :: 'r' :: []
  else bif decide (32 ≤ n) && decide (n ≤ 126) then c :: []
  else hex_escape c

def string_body : Str → Str
  | [] => []
  | c :: s' => string_byte c ++ string_body s'

def string_literal (s : Str) : Str :=
  dquote_c :: (string_body s ++ dquote_c :: [])

def signed_Z (z : Int) : Str :=
  bif decide (z < 0) then '-' :: Decimal.integer (-z) else Decimal.integer z

/-- The exponent field carries an explicit sign, so every canonical float spelling is self-delimiting. -/
def signed_exp (e : Int) : Str :=
  bif decide (e < 0) then '-' :: Decimal.integer (-e) else '+' :: Decimal.integer e

/-- The one canonical decimal float spelling: `0.0`, or `<coefficient>.0e<signed exponent>`. -/
def decimal (d : Float.Decimal) : Str :=
  bif decide (Float.coefficient d = 0) then str! "0.0"
  else signed_Z (Float.coefficient d) ++ str! ".0e" ++ signed_exp (Float.exponent d)

/-- A type use renders its retained ordinary source identifier. -/
def render_type_expr (t : Syntax.TypeExpr) : Str :=
  Names.render_ordinary (Syntax.type_expr_ident t)

/-- A binding name renders its identifier, or the blank underscore. -/
def render_binding_name (b : Syntax.BindingName) : Str :=
  match b with | Syntax.BNamed n => Names.render_ordinary n | Syntax.BBlank => str! "_"

/-- A source literal renders its magnitude with no sign, or its canonical Go interpreted string. -/
def render_literal (l : Syntax.Literal) : Str :=
  match l with
  | Syntax.IntegerLiteral n => Decimal.integer (n : Int)
  | Syntax.FloatLiteral d   => decimal (Float.nnd_decimal d)
  | Syntax.StringLiteral s  => string_literal s

def expr_is_unary (e : Expr) : Bool :=
  match e with
  | Unary _ _ => true
  | Name _ => false
  | LiteralExpr _ => false
  | Application _ _ => false

/-- One comma-joined argument list, parameterized by the element renderer, so there is a single traversal. -/
def render_arglist (render_elem : Expr → Str) : List Expr → Str
  | []      => str! ""
  | x :: xs => render_elem x ++ (match xs with | [] => str! "" | _ :: _ => str! ", " ++ render_arglist render_elem xs)

mutual
/-- A unary operand or application head that is itself unary is parenthesized, so the source cannot spell
    `--`. -/
def render_expr : Expr → Str
  | Name n => Names.render_ordinary n
  | LiteralExpr l => render_literal l
  | Unary Syntax.UnaryMinus e' =>
      str! "-" ++ (bif expr_is_unary e' then str! "(" ++ render_expr e' ++ str! ")" else render_expr e')
  | Application head args =>
      (bif expr_is_unary head then str! "(" ++ render_expr head ++ str! ")" else render_expr head)
      ++ str! "(" ++ render_args args ++ str! ")"
/-- The one argument renderer both the application case and declaration rendering call. -/
def render_args : List Expr → Str
  | []      => str! ""
  | x :: xs => render_expr x ++ (match xs with | [] => str! "" | _ :: _ => str! ", " ++ render_args xs)
end

-- The `.v`'s definition of `render_args`, as an equation.
private theorem render_args_arglist : ∀ es, render_args es = render_arglist render_expr es
  | [] => rfl
  | x :: xs => by
    cases xs with
    | nil => rfl
    | cons y ys =>
      show render_expr x ++ (str! ", " ++ render_args (y :: ys))
        = render_expr x ++ (str! ", " ++ render_arglist render_expr (y :: ys))
      rw [render_args_arglist (y :: ys)]

theorem render_app : ∀ head args,
    render_expr (Application head args)
    = (bif expr_is_unary head then str! "(" ++ render_expr head ++ str! ")" else render_expr head)
      ++ str! "(" ++ render_args args ++ str! ")" := fun _ _ => rfl

def render_names : List Syntax.BindingName → Str
  | []       => str! ""
  | [b]      => render_binding_name b
  | b :: b2 :: bs' => render_binding_name b ++ str! ", " ++ render_names (b2 :: bs')
def render_ne_names (bs : Collections.NonEmpty Syntax.BindingName) : Str :=
  render_names (Collections.ne_to_list bs)
def render_ne_exprs (es : Collections.NonEmpty Expr) : Str :=
  render_args (Collections.ne_to_list es)
def render_opt_type (t : Option Syntax.TypeExpr) : Str :=
  match t with | some ty => str! " " ++ render_type_expr ty | none => str! ""

def render_const_spec (s : Syntax.ConstSpec) : Str :=
  render_ne_names (Syntax.const_names s) ++
  match Syntax.const_init s with
  | Syntax.ExplicitConstInit ty vs => render_opt_type ty ++ str! " = " ++ render_ne_exprs vs
  | Syntax.InheritedConstInit => str! ""
def render_var_spec (s : Syntax.VarSpec) : Str :=
  render_ne_names (Syntax.var_names s) ++
  match Syntax.var_init s with
  | Syntax.VarTypeOnly ty => str! " " ++ render_type_expr ty
  | Syntax.VarValues ty vs => render_opt_type ty ++ str! " = " ++ render_ne_exprs vs
def render_type_spec (s : Syntax.TypeSpec) : Str :=
  match s with
  | Syntax.AliasSpec nm ty => render_binding_name nm ++ str! " = " ++ render_type_expr ty
  | Syntax.DefSpec nm ty   => render_binding_name nm ++ str! " " ++ render_type_expr ty

/-- One tab per nesting depth; a grouped declaration indents its inner lines by construction. -/
def indent : Nat → Str | 0 => str! "" | d + 1 => tab ++ indent d

def render_spec_lines {A : Type} (render : A → Str) (depth : Nat) : List A → Str
  | [] => str! ""
  | s :: rest => indent depth ++ render s ++ nl ++ render_spec_lines render depth rest

/-- One spec renders ungrouped; zero or two-or-more render as a parenthesized group, both valid Go. -/
def render_group {A : Type} (kw : Str) (render : A → Str) (depth : Nat) (specs : List A) : Str :=
  match specs with
  | [s] => kw ++ str! " " ++ render s
  | []  => kw ++ str! " (" ++ nl ++ render_spec_lines render (depth + 1) [] ++ indent depth ++ str! ")"
  | s :: s2 :: rest =>
      kw ++ str! " (" ++ nl ++ render_spec_lines render (depth + 1) (s :: s2 :: rest) ++ indent depth ++ str! ")"

def render_declaration (depth : Nat) (d : Syntax.Declaration) : Str :=
  match d with
  | Syntax.ConstDecl specs => render_group (str! "const") render_const_spec depth specs
  | Syntax.VarDecl specs   => render_group (str! "var") render_var_spec depth specs
  | Syntax.TypeDecl specs  => render_group (str! "type") render_type_spec depth specs

def render_stmt (depth : Nat) (s : Syntax.Stmt) : Str :=
  indent depth ++
  (match s with
   | Syntax.ExprStmt e => render_expr e
   | Syntax.DeclarationStmt d => render_declaration depth d
   | Syntax.ShortVarDecl names vs => render_ne_names names ++ str! " := " ++ render_ne_exprs vs) ++ nl

def render_stmts (depth : Nat) : List Syntax.Stmt → Str
  | [] => str! "" | s :: rest => render_stmt depth s ++ render_stmts depth rest

def render_block (depth : Nat) (b : Syntax.Block) : Str :=
  match b with | Syntax.MakeBlock ss => render_stmts depth ss

def render_top_level_decl (t : Syntax.TopLevelDecl) : Str :=
  match t with
  | Syntax.TopDeclaration d => render_declaration 0 d ++ nl
  | Syntax.Main body => str! "func main() {" ++ nl ++ render_block 1 body ++ str! "}" ++ nl

/-- Each top-level declaration is preceded by a blank line, matching gofmt spacing. -/
def render_top_levels : List Syntax.TopLevelDecl → Str
  | [] => str! "" | t :: rest => nl ++ render_top_level_decl t ++ render_top_levels rest

/-- The package clause as rendered bytes, owned by the source rather than derived. -/
def package_clause (pc : Syntax.PackageClause) : Str :=
  match pc with | Syntax.MainPackage => str! "main"

/-- `file` consumes the import list structurally, so a future constructor forces a renderer update. -/
def import_spec (i : Syntax.ImportSpec) : Str := nomatch i
def imports : List Syntax.ImportSpec → Str
  | [] => str! "" | i :: rest => import_spec i ++ imports rest

theorem imports_nil_bytes : ∀ xs, imports xs = str! "" := by
  intro xs
  cases xs with
  | nil => rfl
  | cons i _ => exact nomatch i

def file (f : Syntax.File) : Str :=
  header ++ nl_c :: (nl ++ str! "package " ++ package_clause (Syntax.package f) ++ nl
                        ++ imports (Syntax.imports f)
                        ++ render_top_levels (Syntax.declarations f))

/-- The header is exactly the first line, which is strictly stronger than being a prefix. -/
theorem file_first_line : ∀ f, ∃ rest, file f = header ++ nl_c :: rest := fun _ => ⟨_, rfl⟩

/-- The canonical go.mod: the header line, then `module <path>` and `go <version>`, and nothing else. -/
def module_file (ms : Syntax.ModuleSpec) : Str :=
  header ++ nl_c ::
    (nl ++ str! "module " ++ ModulePath.text (Syntax.module_path ms) ++ nl ++ nl
        ++ str! "go " ++ Version.render (Syntax.module_version ms) ++ nl)

theorem module_file_first_line : ∀ ms, ∃ rest, module_file ms = header ++ nl_c :: rest := fun _ => ⟨_, rfl⟩

theorem module_file_exact : ∀ ms,
    module_file ms = header ++ nl_c ::
      (nl ++ str! "module " ++ ModulePath.text (Syntax.module_path ms) ++ nl ++ nl
          ++ str! "go " ++ Version.render (Syntax.module_version ms) ++ nl) := fun _ => rfl


-- Rocq: `Bool.andb_true_iff` / `Bool.orb_true_iff`, one direction each, by cases (Names.lean).
private theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h

theorem str_ascii_app : ∀ a b, Names.str_ascii (a ++ b) = (Names.str_ascii a && Names.str_ascii b) := by
  intro a b
  induction a with
  | nil => rfl
  | cons c a' IH =>
    show (Names.is_ascii_c c && Names.str_ascii (a' ++ b))
      = ((Names.is_ascii_c c && Names.str_ascii a') && Names.str_ascii b)
    rw [IH, Bool.and_assoc]

theorem render_type_expr_ascii : ∀ t, Names.str_ascii (render_type_expr t) = true :=
  fun t => Names.render_ordinary_ascii (Syntax.type_expr_ident t)

theorem render_binding_name_ascii : ∀ b, Names.str_ascii (render_binding_name b) = true := by
  intro b
  cases b with
  | BNamed n => exact Names.render_ordinary_ascii n
  | BBlank => decide

theorem str_ascii_cons : ∀ c s, Names.str_ascii (c :: s) = (Names.is_ascii_c c && Names.str_ascii s) :=
  fun _ _ => rfl

theorem digit_ascii : ∀ d, d < 10 → Names.is_ascii_c (Decimal.digit d) = true := by decide

theorem digits_step : ∀ dig a ds acc,
    Decimal.render dig (a :: ds) acc = Decimal.render dig ds (dig a :: acc) := fun _ _ _ _ => rfl

theorem digits_ascii : ∀ ds acc,
    (∀ d ∈ ds, Names.is_ascii_c (Decimal.digit d) = true) →
    Names.str_ascii (Decimal.render Decimal.digit ds acc) = Names.str_ascii acc := by
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons a ds' IH =>
    intro acc Hall
    rw [digits_step, IH _ (fun d Hd => Hall d (List.Mem.tail _ Hd))]
    show (Names.is_ascii_c (Decimal.digit a) && Names.str_ascii acc) = Names.str_ascii acc
    rw [Hall a (List.Mem.head _)]
    rfl

theorem positive_ascii : ∀ p, 0 < p → Names.str_ascii (Decimal.positive p) = true := by
  intro p Hp
  unfold Decimal.positive
  rw [digits_ascii]
  · rfl
  · intro d Hd
    exact digit_ascii d (Decimal.positive_digits_bound 10 p (by decide) Hp d Hd)

theorem integer_ascii : ∀ z, Names.str_ascii (Decimal.integer z) = true := by
  intro z
  match z with
  | .ofNat 0 => decide
  | .ofNat (n + 1) => exact positive_ascii (n + 1) (Nat.succ_pos n)
  | .negSucc n =>
    show Names.str_ascii (str! "-" ++ Decimal.positive (n + 1)) = true
    rw [str_ascii_app, positive_ascii (n + 1) (Nat.succ_pos n)]
    rfl

/-! String rendering stays ASCII even for high bytes, which appear only as `\xhh` escapes. -/

-- Degenerate under the mapping (divergences): the bound is the hypothesis.
theorem nat_of_ascii_lt_256 : ∀ c : Char, c.toNat < 256 → c.toNat < 256 := fun _ h => h

theorem hex_digit_ascii : ∀ k, k < 16 → Names.is_ascii_c (hex_digit k) = true := by decide

theorem hex_escape_ascii : ∀ c : Char, c.toNat < 256 → Names.str_ascii (hex_escape c) = true := by
  intro c Hb
  have Hhi : c.toNat / 16 < 16 := (Nat.div_lt_iff_lt_mul (by decide)).2 Hb
  have Hlo : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  show (Names.is_ascii_c bslash_c && (Names.is_ascii_c 'x'
    && (Names.is_ascii_c (hex_digit (c.toNat / 16)) && (Names.is_ascii_c (hex_digit (c.toNat % 16)) && true)))) = true
  rw [hex_digit_ascii _ Hhi, hex_digit_ascii _ Hlo]
  decide

theorem string_byte_ascii : ∀ c : Char, c.toNat < 256 → Names.str_ascii (string_byte c) = true := by
  intro c Hb
  unfold string_byte
  dsimp only
  cases decide (c.toNat = 34) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 92) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 10) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 9) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 13) with
  | true => rfl
  | false =>
  cases Hp : (decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126)) with
  | true =>
    show (Names.is_ascii_c c && true) = true
    have Hle : c.toNat ≤ 126 := of_decide_eq_true (band_true Hp).2
    unfold Names.is_ascii_c
    rw [decide_eq_true (Nat.lt_of_le_of_lt Hle (by decide))]
    rfl
  | false => exact hex_escape_ascii c Hb

theorem string_body_ascii : ∀ s : Str, (∀ c ∈ s, c.toNat < 256) → Names.str_ascii (string_body s) = true := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s' IH =>
    intro Hall
    show Names.str_ascii (string_byte c ++ string_body s') = true
    rw [str_ascii_app, string_byte_ascii c (Hall c (List.Mem.head _)),
      IH (fun d Hd => Hall d (List.Mem.tail _ Hd))]
    rfl

theorem string_literal_ascii : ∀ s : Str, (∀ c ∈ s, c.toNat < 256) →
    Names.str_ascii (string_literal s) = true := by
  intro s H
  show (Names.is_ascii_c dquote_c && Names.str_ascii (string_body s ++ dquote_c :: [])) = true
  rw [str_ascii_app, string_body_ascii s H]
  decide

theorem signed_Z_ascii : ∀ z, Names.str_ascii (signed_Z z) = true := by
  intro z
  unfold signed_Z
  cases decide (z < 0) with
  | true =>
    show (Names.is_ascii_c '-' && Names.str_ascii (Decimal.integer (-z))) = true
    rw [integer_ascii]
    rfl
  | false => exact integer_ascii z

theorem signed_exp_ascii : ∀ e, Names.str_ascii (signed_exp e) = true := by
  intro e
  unfold signed_exp
  cases decide (e < 0) with
  | true =>
    show (Names.is_ascii_c '-' && Names.str_ascii (Decimal.integer (-e))) = true
    rw [integer_ascii]
    rfl
  | false =>
    show (Names.is_ascii_c '+' && Names.str_ascii (Decimal.integer e)) = true
    rw [integer_ascii]
    rfl

theorem decimal_ascii : ∀ d, Names.str_ascii (decimal d) = true := by
  intro d
  unfold decimal
  cases decide (Float.coefficient d = 0) with
  | true => rfl
  | false =>
    show Names.str_ascii (signed_Z (Float.coefficient d) ++ str! ".0e" ++ signed_exp (Float.exponent d)) = true
    rw [str_ascii_app, str_ascii_app, signed_Z_ascii, signed_exp_ascii]
    decide

/-! ### The byte-string predicates (divergences: the bound, over an AST) -/

def literal_bytes (l : Syntax.Literal) : Prop :=
  match l with
  | Syntax.IntegerLiteral _ => True
  | Syntax.FloatLiteral _ => True
  | Syntax.StringLiteral s => ∀ c ∈ s, c.toNat < 256

mutual
def expr_bytes : Expr → Prop
  | Name _ => True
  | LiteralExpr l => literal_bytes l
  | Unary _ e => expr_bytes e
  | Application head args => expr_bytes head ∧ exprs_bytes args
def exprs_bytes : List Expr → Prop
  | [] => True
  | e :: es => expr_bytes e ∧ exprs_bytes es
end

private theorem exprs_bytes_mem : ∀ es, exprs_bytes es → ∀ e ∈ es, expr_bytes e := by
  intro es
  induction es with
  | nil => intro _ e He; exact nomatch He
  | cons x xs IH =>
    intro H e He
    cases He with
    | head => exact H.1
    | tail _ He' => exact IH H.2 e He'

def const_spec_bytes (s : Syntax.ConstSpec) : Prop :=
  match Syntax.const_init s with
  | Syntax.ExplicitConstInit _ vs => exprs_bytes (Collections.ne_to_list vs)
  | Syntax.InheritedConstInit => True
def var_spec_bytes (s : Syntax.VarSpec) : Prop :=
  match Syntax.var_init s with
  | Syntax.VarTypeOnly _ => True
  | Syntax.VarValues _ vs => exprs_bytes (Collections.ne_to_list vs)
def declaration_bytes (d : Syntax.Declaration) : Prop :=
  match d with
  | Syntax.ConstDecl specs => ∀ s ∈ specs, const_spec_bytes s
  | Syntax.VarDecl specs => ∀ s ∈ specs, var_spec_bytes s
  | Syntax.TypeDecl _ => True
def stmt_bytes (s : Syntax.Stmt) : Prop :=
  match s with
  | Syntax.ExprStmt e => expr_bytes e
  | Syntax.DeclarationStmt d => declaration_bytes d
  | Syntax.ShortVarDecl _ vs => exprs_bytes (Collections.ne_to_list vs)
def block_bytes (b : Syntax.Block) : Prop :=
  match b with | Syntax.MakeBlock ss => ∀ s ∈ ss, stmt_bytes s
def top_level_decl_bytes (t : Syntax.TopLevelDecl) : Prop :=
  match t with
  | Syntax.TopDeclaration d => declaration_bytes d
  | Syntax.Main body => block_bytes body
def file_bytes (f : Syntax.File) : Prop := ∀ t ∈ Syntax.declarations f, top_level_decl_bytes t

theorem render_literal_ascii : ∀ l, literal_bytes l → Names.str_ascii (render_literal l) = true := by
  intro l H
  cases l with
  | IntegerLiteral n => exact integer_ascii (n : Int)
  | FloatLiteral d => exact decimal_ascii _
  | StringLiteral s => exact string_literal_ascii s H

theorem render_args_ascii_of : ∀ es,
    (∀ e ∈ es, Names.str_ascii (render_expr e) = true) →
    Names.str_ascii (render_args es) = true := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es' IH =>
    intro HF
    have Hx := HF e (List.Mem.head _)
    have Hxs := fun x Hx => HF x (List.Mem.tail _ Hx)
    cases es' with
    | nil =>
      show Names.str_ascii (render_expr e ++ str! "") = true
      rw [str_ascii_app, Hx]
      rfl
    | cons e2 es'' =>
      show Names.str_ascii (render_expr e ++ (str! ", " ++ render_args (e2 :: es''))) = true
      rw [str_ascii_app, str_ascii_app, Hx, IH Hxs]
      rfl

theorem render_expr_ascii : ∀ e, expr_bytes e → Names.str_ascii (render_expr e) = true := by
  refine Syntax.Expr_ind' (fun e => expr_bytes e → Names.str_ascii (render_expr e) = true) ?_ ?_ ?_ ?_
  · intro n _; exact Names.render_ordinary_ascii n
  · intro l Hl; exact render_literal_ascii l Hl
  · intro op e IH He
    cases op
    have IH' := IH He
    show Names.str_ascii (str! "-" ++ (bif expr_is_unary e then str! "(" ++ render_expr e ++ str! ")"
      else render_expr e)) = true
    cases expr_is_unary e with
    | true =>
      dsimp only [cond]
      rw [str_ascii_app, str_ascii_app, str_ascii_app, IH']
      rfl
    | false =>
      dsimp only [cond]
      rw [str_ascii_app, IH']
      rfl
  · intro head args IHhead IHargs H
    rw [render_app]
    have Hh := IHhead H.1
    have Ha := render_args_ascii_of args (fun x Hx => IHargs x Hx (exprs_bytes_mem args H.2 x Hx))
    rw [str_ascii_app, str_ascii_app, str_ascii_app, Ha]
    cases expr_is_unary head with
    | true =>
      dsimp only [cond]
      rw [str_ascii_app, str_ascii_app, Hh]
      rfl
    | false =>
      dsimp only [cond]
      rw [Hh]
      rfl

theorem render_args_ascii : ∀ es, exprs_bytes es → Names.str_ascii (render_args es) = true :=
  fun es H => render_args_ascii_of es (fun e He => render_expr_ascii e (exprs_bytes_mem es H e He))

theorem render_names_ascii : ∀ bs, Names.str_ascii (render_names bs) = true := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b bs' IH =>
    cases bs' with
    | nil => exact render_binding_name_ascii b
    | cons b2 bs'' =>
      show Names.str_ascii (render_binding_name b ++ str! ", " ++ render_names (b2 :: bs'')) = true
      rw [str_ascii_app, str_ascii_app, render_binding_name_ascii, IH]
      rfl

theorem render_ne_names_ascii : ∀ bs, Names.str_ascii (render_ne_names bs) = true :=
  fun bs => render_names_ascii (Collections.ne_to_list bs)
theorem render_ne_exprs_ascii : ∀ es, exprs_bytes (Collections.ne_to_list es) →
    Names.str_ascii (render_ne_exprs es) = true :=
  fun es H => render_args_ascii (Collections.ne_to_list es) H
theorem render_opt_type_ascii : ∀ t, Names.str_ascii (render_opt_type t) = true := by
  intro t
  cases t with
  | some ty =>
    show Names.str_ascii (str! " " ++ render_type_expr ty) = true
    rw [str_ascii_app, render_type_expr_ascii]
    rfl
  | none => rfl

theorem render_const_spec_ascii : ∀ s, const_spec_bytes s → Names.str_ascii (render_const_spec s) = true := by
  intro s H
  unfold render_const_spec
  rw [str_ascii_app, render_ne_names_ascii]
  unfold const_spec_bytes at H
  revert H
  cases Syntax.const_init s with
  | ExplicitConstInit ty vs =>
    intro H
    show (true && Names.str_ascii (render_opt_type ty ++ str! " = " ++ render_ne_exprs vs)) = true
    rw [str_ascii_app, str_ascii_app, render_opt_type_ascii, render_ne_exprs_ascii vs H]
    rfl
  | InheritedConstInit => intro _; rfl

theorem render_var_spec_ascii : ∀ s, var_spec_bytes s → Names.str_ascii (render_var_spec s) = true := by
  intro s H
  unfold render_var_spec
  rw [str_ascii_app, render_ne_names_ascii]
  unfold var_spec_bytes at H
  revert H
  cases Syntax.var_init s with
  | VarTypeOnly ty =>
    intro _
    show (true && Names.str_ascii (str! " " ++ render_type_expr ty)) = true
    rw [str_ascii_app, render_type_expr_ascii]
    rfl
  | VarValues ty vs =>
    intro H
    show (true && Names.str_ascii (render_opt_type ty ++ str! " = " ++ render_ne_exprs vs)) = true
    rw [str_ascii_app, str_ascii_app, render_opt_type_ascii, render_ne_exprs_ascii vs H]
    rfl

theorem render_type_spec_ascii : ∀ s, Names.str_ascii (render_type_spec s) = true := by
  intro s
  cases s with
  | AliasSpec nm ty =>
    show Names.str_ascii (render_binding_name nm ++ str! " = " ++ render_type_expr ty) = true
    rw [str_ascii_app, str_ascii_app, render_binding_name_ascii, render_type_expr_ascii]
    rfl
  | DefSpec nm ty =>
    show Names.str_ascii (render_binding_name nm ++ str! " " ++ render_type_expr ty) = true
    rw [str_ascii_app, str_ascii_app, render_binding_name_ascii, render_type_expr_ascii]
    rfl

theorem indent_ascii : ∀ d, Names.str_ascii (indent d) = true := by
  intro d
  induction d with
  | zero => rfl
  | succ d IH =>
    show Names.str_ascii (tab ++ indent d) = true
    rw [str_ascii_app, IH]
    rfl

private theorem render_spec_lines_ascii_mem {A : Type} (render : A → Str) (depth : Nat) :
    ∀ specs, (∀ s ∈ specs, Names.str_ascii (render s) = true) →
    Names.str_ascii (render_spec_lines render depth specs) = true := by
  intro specs
  induction specs with
  | nil => intro _; rfl
  | cons s rest IH =>
    intro Hr
    show Names.str_ascii (indent depth ++ render s ++ nl ++ render_spec_lines render depth rest) = true
    rw [str_ascii_app, str_ascii_app, str_ascii_app, indent_ascii, Hr s (List.Mem.head _),
      IH (fun x Hx => Hr x (List.Mem.tail _ Hx))]
    rfl

theorem render_spec_lines_ascii {A : Type} (render : A → Str) (depth : Nat) :
    (∀ s, Names.str_ascii (render s) = true) →
    ∀ specs, Names.str_ascii (render_spec_lines render depth specs) = true :=
  fun Hr specs => render_spec_lines_ascii_mem render depth specs (fun s _ => Hr s)

private theorem render_group_ascii_mem {A : Type} (kw : Str) (render : A → Str) (depth : Nat) :
    Names.str_ascii kw = true →
    ∀ specs, (∀ s ∈ specs, Names.str_ascii (render s) = true) →
    Names.str_ascii (render_group kw render depth specs) = true := by
  intro Hkw specs Hr
  cases specs with
  | nil =>
    show Names.str_ascii (kw ++ str! " (" ++ nl ++ render_spec_lines render (depth + 1) []
      ++ indent depth ++ str! ")") = true
    rw [str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, Hkw,
      render_spec_lines_ascii_mem render (depth + 1) [] Hr, indent_ascii]
    decide
  | cons s rest =>
    cases rest with
    | nil =>
      show Names.str_ascii (kw ++ str! " " ++ render s) = true
      rw [str_ascii_app, str_ascii_app, Hkw, Hr s (List.Mem.head _)]
      decide
    | cons s2 rest' =>
      show Names.str_ascii (kw ++ str! " (" ++ nl ++ render_spec_lines render (depth + 1) (s :: s2 :: rest')
        ++ indent depth ++ str! ")") = true
      rw [str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, Hkw,
        render_spec_lines_ascii_mem render (depth + 1) (s :: s2 :: rest') Hr, indent_ascii]
      decide

theorem render_group_ascii {A : Type} (kw : Str) (render : A → Str) (depth : Nat) :
    Names.str_ascii kw = true →
    (∀ s, Names.str_ascii (render s) = true) →
    ∀ specs, Names.str_ascii (render_group kw render depth specs) = true :=
  fun Hkw Hr specs => render_group_ascii_mem kw render depth Hkw specs (fun s _ => Hr s)

theorem render_declaration_ascii : ∀ depth d, declaration_bytes d →
    Names.str_ascii (render_declaration depth d) = true := by
  intro depth d H
  cases d with
  | ConstDecl specs =>
    exact render_group_ascii_mem _ _ depth (by decide) specs (fun s Hs => render_const_spec_ascii s (H s Hs))
  | VarDecl specs =>
    exact render_group_ascii_mem _ _ depth (by decide) specs (fun s Hs => render_var_spec_ascii s (H s Hs))
  | TypeDecl specs =>
    exact render_group_ascii _ _ depth (by decide) render_type_spec_ascii specs

theorem render_stmt_ascii : ∀ depth s, stmt_bytes s → Names.str_ascii (render_stmt depth s) = true := by
  intro depth s H
  cases s with
  | ExprStmt e =>
    show Names.str_ascii (indent depth ++ render_expr e ++ nl) = true
    rw [str_ascii_app, str_ascii_app, indent_ascii, render_expr_ascii e H]
    decide
  | DeclarationStmt d =>
    show Names.str_ascii (indent depth ++ render_declaration depth d ++ nl) = true
    rw [str_ascii_app, str_ascii_app, indent_ascii, render_declaration_ascii depth d H]
    decide
  | ShortVarDecl names vs =>
    show Names.str_ascii (indent depth ++ (render_ne_names names ++ str! " := " ++ render_ne_exprs vs) ++ nl) = true
    rw [str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, indent_ascii, render_ne_names_ascii,
      render_ne_exprs_ascii vs H]
    decide

theorem render_stmts_ascii : ∀ depth ss, (∀ s ∈ ss, stmt_bytes s) →
    Names.str_ascii (render_stmts depth ss) = true := by
  intro depth ss
  induction ss with
  | nil => intro _; rfl
  | cons s ss' IH =>
    intro H
    show Names.str_ascii (render_stmt depth s ++ render_stmts depth ss') = true
    rw [str_ascii_app, render_stmt_ascii depth s (H s (List.Mem.head _)),
      IH (fun x Hx => H x (List.Mem.tail _ Hx))]
    rfl

theorem render_block_ascii : ∀ depth b, block_bytes b → Names.str_ascii (render_block depth b) = true := by
  intro depth b H
  cases b with
  | MakeBlock ss => exact render_stmts_ascii depth ss H

theorem render_top_level_decl_ascii : ∀ t, top_level_decl_bytes t →
    Names.str_ascii (render_top_level_decl t) = true := by
  intro t H
  cases t with
  | TopDeclaration d =>
    show Names.str_ascii (render_declaration 0 d ++ nl) = true
    rw [str_ascii_app, render_declaration_ascii 0 d H]
    decide
  | Main body =>
    show Names.str_ascii (str! "func main() {" ++ nl ++ render_block 1 body ++ str! "}" ++ nl) = true
    rw [str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, render_block_ascii 1 body H]
    decide

theorem render_top_levels_ascii : ∀ ts, (∀ t ∈ ts, top_level_decl_bytes t) →
    Names.str_ascii (render_top_levels ts) = true := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t ts' IH =>
    intro H
    show Names.str_ascii (nl ++ render_top_level_decl t ++ render_top_levels ts') = true
    rw [str_ascii_app, str_ascii_app, render_top_level_decl_ascii t (H t (List.Mem.head _)),
      IH (fun x Hx => H x (List.Mem.tail _ Hx))]
    decide

theorem imports_ascii : ∀ xs, Names.str_ascii (imports xs) = true := by
  intro xs; rw [imports_nil_bytes]; rfl

theorem file_ascii : ∀ f, file_bytes f → Names.str_ascii (file f) = true := by
  intro f H
  unfold file
  rw [str_ascii_app, str_ascii_cons, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app,
    render_top_levels_ascii _ H, imports_ascii]
  cases Syntax.package f
  decide


theorem all_path_chars_ascii : ∀ s, ModulePath.all_path_chars s = true → Names.str_ascii s = true := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s' IH =>
    intro H
    obtain ⟨Hc, Hs⟩ := band_true H
    show (Names.is_ascii_c c && Names.str_ascii s') = true
    unfold Names.is_ascii_c
    rw [decide_eq_true (ModulePath.path_char_lt_128 c Hc), IH Hs]
    rfl

theorem module_path_text_ascii : ∀ p, Names.str_ascii (ModulePath.text p) = true :=
  fun p => all_path_chars_ascii _ (ModulePath.path_ok_all_chars _ (ModulePath.valid p))

theorem module_file_ascii : ∀ ms, Names.str_ascii (module_file ms) = true := by
  intro ms
  unfold module_file
  rw [str_ascii_app, str_ascii_cons, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app, str_ascii_app,
    str_ascii_app, str_ascii_app, module_path_text_ascii]
  cases Syntax.module_version ms
  decide

/-! Decimal faithfulness: an emitted decimal denotes exactly its value, with no leading zero. -/

def ascii_digit (c : Char) : Nat := c.toNat - 48

def dval : Str → Int → Int
  | [], acc => acc
  | c :: s', acc => dval s' (acc * 10 + (ascii_digit c : Int))
def dval0 (s : Str) : Int := dval s 0

theorem ascii_digit_is_digit : ∀ d, d < 10 → ascii_digit (Decimal.digit d) = d := by decide

theorem digits_dval : ∀ ds base,
    (∀ d ∈ ds, d < 10) →
    dval (Decimal.render Decimal.digit ds base) 0 = dval base (Decimal.value 10 ds) := by
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds' IH =>
    intro base Hall
    rw [digits_step, IH _ (fun x Hx => Hall x (List.Mem.tail _ Hx))]
    show dval base (Decimal.value 10 ds' * 10 + (ascii_digit (Decimal.digit d) : Int))
      = dval base ((d : Int) + 10 * Decimal.value 10 ds')
    rw [ascii_digit_is_digit d (Hall d (List.Mem.head _))]
    exact congrArg (dval base) (by omega)

theorem positive_digit_value : ∀ p, 0 < p → dval0 (Decimal.positive p) = (p : Int) := by
  intro p Hp
  unfold dval0 Decimal.positive
  rw [digits_dval _ _ (fun d Hd => Decimal.positive_digits_bound 10 p (by decide) Hp d Hd)]
  exact Decimal.positive_digits_val 10 p (by decide) Hp

theorem integer_decimal_faithful : ∀ z, 0 ≤ z → dval0 (Decimal.integer z) = z := by
  intro z H
  match z, H with
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), _ => exact positive_digit_value (n + 1) (Nat.succ_pos n)
  | .negSucc _, H => exact absurd H (by omega)

def head_not_zero (s : Str) : Prop :=
  match s with | [] => False | c :: _ => c ≠ Decimal.digit 0

-- Rocq: `fold_left_app`, by induction (core's `List.foldl_append` carries `propext` and `Quot.sound`).
private theorem foldl_append {α β : Type} (f : α → β → α) :
    ∀ (l1 l2 : List β) (a : α), List.foldl f a (l1 ++ l2) = List.foldl f (List.foldl f a l1) l2
  | [], _, _ => rfl
  | x :: xs, l2, a => foldl_append f xs l2 (f a x)

theorem digits_snoc : ∀ ds a base,
    Decimal.render Decimal.digit (ds ++ [a]) base = Decimal.digit a :: Decimal.render Decimal.digit ds base := by
  intro ds a base
  unfold Decimal.render
  rw [foldl_append]
  rfl

-- Rocq: `last_last` / `in_or_app`, by induction (core's `List.getLastD_concat` carries `propext`).
private theorem getLastD_concat {α : Type} (a d : α) : ∀ l : List α, (l ++ [a]).getLastD d = a
  | [] => rfl
  | [_] => rfl
  | _ :: y :: l => getLastD_concat a d (y :: l)
private theorem mem_concat {α : Type} (a : α) : ∀ l : List α, a ∈ l ++ [a]
  | [] => List.Mem.head _
  | _ :: l => List.Mem.tail _ (mem_concat a l)
-- `List.eq_nil_or_concat` speaks of `l.concat a`; the `.v`'s `exists_last` of `l ++ [a]`.
private theorem concat_eq_append {α : Type} (a : α) : ∀ l : List α, l.concat a = l ++ [a]
  | [] => rfl
  | x :: l => congrArg (x :: ·) (concat_eq_append a l)

private theorem digit_ne_zero : ∀ a, a < 10 → 1 ≤ a → Decimal.digit a ≠ Decimal.digit 0 := by decide

theorem positive_no_leading_zero : ∀ p, 0 < p → head_not_zero (Decimal.positive p) := by
  intro p Hp
  unfold Decimal.positive
  rcases List.eq_nil_or_concat (Decimal.positive_digits 10 p) with Hnil | ⟨init, a, Ha⟩
  · exact absurd Hnil (Decimal.positive_digits_nonnil 10 p Hp)
  · rw [concat_eq_append] at Ha
    have Ha1 : 1 ≤ a := by
      have Hl := Decimal.positive_digits_last 10 p (by decide) Hp
      rw [Ha, getLastD_concat] at Hl
      exact Hl
    have Ha10 : a < 10 :=
      Decimal.positive_digits_bound 10 p (by decide) Hp a (by rw [Ha]; exact mem_concat a init)
    rw [Ha, digits_snoc]
    exact digit_ne_zero a Ha10 Ha1

def read_go_int (s : Str) : Int :=
  match s with
  | c :: s' => bif c == '-' then -(dval0 s') else dval0 (c :: s')
  | [] => dval0 []

/-! An independent decoder defined by its own recursion; it is a denotation tool, not a spelling recogniser. -/

def decode_hex_digit (c : Char) : Option Nat :=
  bif decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57) then some (c.toNat - 48)
  else bif decide (97 ≤ c.toNat) && decide (c.toNat ≤ 102) then some (c.toNat - 87)
  else none

def decode_string_body : Str → Option Str
  | [] => none                                                  -- ran off the end without a closing quote
  | c :: rest =>
      bif c == dquote_c then                                    -- closing quote
        (match rest with | [] => some [] | _ :: _ => none)      -- trailing bytes ⇒ reject
      else bif c == bslash_c then                               -- an escape
        (match rest with
         | [] => none
         | e :: rest2 =>
             bif e == dquote_c then Option.map (dquote_c :: ·) (decode_string_body rest2)
             else bif e == bslash_c then Option.map (bslash_c :: ·) (decode_string_body rest2)
             else bif e == 'n' then Option.map (nl_c :: ·) (decode_string_body rest2)
             else bif e == 't' then Option.map (tab_c :: ·) (decode_string_body rest2)
             else bif e == 'r' then Option.map (cr_c :: ·) (decode_string_body rest2)
             else bif e == 'x' then
               (match rest2 with
                | h1 :: h2 :: rest3 =>
                    (match decode_hex_digit h1, decode_hex_digit h2 with
                     | some v1, some v2 =>
                         Option.map (Char.ofNat (v1 * 16 + v2) :: ·) (decode_string_body rest3)
                     | some _, none => none                     -- nonhex digit
                     | none, some _ => none
                     | none, none => none)
                | [] => none                                    -- truncated \x
                | [_] => none)
             else none)                                         -- unknown escape
      else bif decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) then
        Option.map (c :: ·) (decode_string_body rest)           -- a directly-emitted printable byte
      else none                                                 -- an unescaped control/newline byte ⇒ reject

def decode_string_literal (s : Str) : Option Str :=
  match s with
  | c :: rest => bif c == dquote_c then decode_string_body rest else none
  | [] => none

theorem str_app_assoc : ∀ a b d : Str, a ++ (b ++ d) = (a ++ b) ++ d := by
  intro a
  induction a with
  | nil => intro _ _; rfl
  | cons c a' IH => intro b d; show c :: (a' ++ (b ++ d)) = c :: ((a' ++ b) ++ d); rw [IH]

theorem hex_digit_decode : ∀ k, k < 16 → decode_hex_digit (hex_digit k) = some k := by decide

theorem byte_reconstruct : ∀ c : Char, Char.ofNat (c.toNat / 16 * 16 + c.toNat % 16) = c := by
  intro c
  have H : c.toNat / 16 * 16 + c.toNat % 16 = c.toNat := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  rw [H]
  exact Char.ofNat_toNat c

-- The `\x` arm of `decode_string_body`, by unfolding (Rocq: `cbn` with `hex_digit` opaque).
private theorem decode_hex_case : ∀ h1 h2 rest3,
    decode_string_body (bslash_c :: 'x' :: h1 :: h2 :: rest3)
    = match decode_hex_digit h1, decode_hex_digit h2 with
      | some v1, some v2 => Option.map (Char.ofNat (v1 * 16 + v2) :: ·) (decode_string_body rest3)
      | some _, none => none
      | none, some _ => none
      | none, none => none := fun _ _ _ => rfl

theorem decode_hex_prefix : ∀ hi lo tail,
    hi < 16 → lo < 16 →
    decode_string_body (bslash_c :: 'x' :: hex_digit hi :: hex_digit lo :: tail)
    = Option.map (Char.ofNat (hi * 16 + lo) :: ·) (decode_string_body tail) := by
  intro hi lo tail Hhi Hlo
  rw [decode_hex_case, hex_digit_decode hi Hhi, hex_digit_decode lo Hlo]

theorem hex_escape_exact : ∀ (c : Char) tail, c.toNat < 256 →
    decode_string_body (hex_escape c ++ tail) = Option.map (c :: ·) (decode_string_body tail) := by
  intro c tail Hb
  have Hhi : c.toNat / 16 < 16 := (Nat.div_lt_iff_lt_mul (by decide)).2 Hb
  have Hlo : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  show decode_string_body (bslash_c :: 'x' :: hex_digit (c.toNat / 16) :: hex_digit (c.toNat % 16) :: tail)
    = Option.map (c :: ·) (decode_string_body tail)
  rw [decode_hex_prefix _ _ _ Hhi Hlo, byte_reconstruct]

-- Rocq: `replace c with dquote_c by (… ascii_nat_embedding)`.
private theorem char_of_toNat : ∀ (c : Char) (n : Nat), c.toNat = n → c = Char.ofNat n :=
  fun c _ h => (Char.ofNat_toNat c).symm.trans (congrArg Char.ofNat h)

-- The five one-letter escapes decode to their byte.  `decode_string_body` on a cons with a variable tail does
-- not unfold under `rfl` (the unifier stalls on the recursive call), so this goes through the proven
-- `decode_string_body.eq_def` instead.
private theorem decode_simple_escape : ∀ (e d : Char) tail,
    (bif e == dquote_c then some dquote_c else bif e == bslash_c then some bslash_c
     else bif e == 'n' then some nl_c else bif e == 't' then some tab_c
     else bif e == 'r' then some cr_c else none) = some d →
    decode_string_body (bslash_c :: e :: tail) = Option.map (d :: ·) (decode_string_body tail) := by
  intro e d tail H
  rw [decode_string_body.eq_def]
  dsimp only
  rw [show (bslash_c == dquote_c) = false from rfl, show (bslash_c == bslash_c) = true from rfl]
  dsimp only [cond]
  revert H
  cases e == dquote_c with
  | true => intro H; dsimp only [cond] at H ⊢; rw [← Option.some.inj H]
  | false =>
  cases e == bslash_c with
  | true => intro H; dsimp only [cond] at H ⊢; rw [← Option.some.inj H]
  | false =>
  cases e == 'n' with
  | true => intro H; dsimp only [cond] at H ⊢; rw [← Option.some.inj H]
  | false =>
  cases e == 't' with
  | true => intro H; dsimp only [cond] at H ⊢; rw [← Option.some.inj H]
  | false =>
  cases e == 'r' with
  | true => intro H; dsimp only [cond] at H ⊢; rw [← Option.some.inj H]
  | false => intro H; dsimp only [cond] at H; exact nomatch H

theorem decode_render_byte : ∀ (c : Char) tail, c.toNat < 256 →
    decode_string_body (string_byte c ++ tail) = Option.map (c :: ·) (decode_string_body tail) := by
  intro c tail Hb
  unfold string_byte
  dsimp only
  cases E34 : decide (c.toNat = 34) with
  | true =>
    rw [char_of_toNat c 34 (of_decide_eq_true E34)]
    show decode_string_body (bslash_c :: dquote_c :: tail) = Option.map (dquote_c :: ·) (decode_string_body tail)
    exact decode_simple_escape _ _ tail rfl
  | false =>
  cases E92 : decide (c.toNat = 92) with
  | true =>
    rw [char_of_toNat c 92 (of_decide_eq_true E92)]
    show decode_string_body (bslash_c :: bslash_c :: tail) = Option.map (bslash_c :: ·) (decode_string_body tail)
    exact decode_simple_escape _ _ tail rfl
  | false =>
  cases E10 : decide (c.toNat = 10) with
  | true =>
    rw [char_of_toNat c 10 (of_decide_eq_true E10)]
    show decode_string_body (bslash_c :: 'n' :: tail) = Option.map (nl_c :: ·) (decode_string_body tail)
    exact decode_simple_escape _ _ tail rfl
  | false =>
  cases E9 : decide (c.toNat = 9) with
  | true =>
    rw [char_of_toNat c 9 (of_decide_eq_true E9)]
    show decode_string_body (bslash_c :: 't' :: tail) = Option.map (tab_c :: ·) (decode_string_body tail)
    exact decode_simple_escape _ _ tail rfl
  | false =>
  cases E13 : decide (c.toNat = 13) with
  | true =>
    rw [char_of_toNat c 13 (of_decide_eq_true E13)]
    show decode_string_body (bslash_c :: 'r' :: tail) = Option.map (cr_c :: ·) (decode_string_body tail)
    exact decode_simple_escape _ _ tail rfl
  | false =>
  cases Hp : (decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126)) with
  | true =>
    have Hnd : (c == dquote_c) = false := by
      cases hq : (c == dquote_c) with
      | false => rfl
      | true =>
        have hc : c = dquote_c := of_decide_eq_true hq
        subst hc
        exact absurd E34 (by decide)
    have Hnb : (c == bslash_c) = false := by
      cases hq : (c == bslash_c) with
      | false => rfl
      | true =>
        have hc : c = bslash_c := of_decide_eq_true hq
        subst hc
        exact absurd E92 (by decide)
    show decode_string_body (c :: tail) = Option.map (c :: ·) (decode_string_body tail)
    rw [decode_string_body.eq_def]
    dsimp only
    rw [Hnd, Hnb, Hp]
    dsimp only [cond]
  | false => exact hex_escape_exact c tail Hb

theorem decode_body_render : ∀ s : Str, (∀ c ∈ s, c.toNat < 256) →
    decode_string_body (string_body s ++ dquote_c :: []) = some s := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s' IH =>
    intro Hall
    show decode_string_body ((string_byte c ++ string_body s') ++ dquote_c :: []) = some (c :: s')
    rw [← str_app_assoc, decode_render_byte c _ (Hall c (List.Mem.head _)),
      IH (fun d Hd => Hall d (List.Mem.tail _ Hd))]
    rfl

theorem string_roundtrip : ∀ s : Str, (∀ c ∈ s, c.toNat < 256) →
    decode_string_literal (string_literal s) = some s := by
  intro s H
  show decode_string_body (string_body s ++ dquote_c :: []) = some s
  exact decode_body_render s H

/-! The literal is quote-delimited and holds no raw newline or carriage return. -/
def byte_not_nl_cr (c : Char) : Bool :=
  !(decide (c.toNat = 10)) && !(decide (c.toNat = 13))
def str_no_nl_cr : Str → Bool
  | [] => true
  | c :: s' => byte_not_nl_cr c && str_no_nl_cr s'

theorem str_no_nl_cr_app : ∀ a b, str_no_nl_cr (a ++ b) = (str_no_nl_cr a && str_no_nl_cr b) := by
  intro a b
  induction a with
  | nil => rfl
  | cons c a' IH =>
    show (byte_not_nl_cr c && str_no_nl_cr (a' ++ b)) = ((byte_not_nl_cr c && str_no_nl_cr a') && str_no_nl_cr b)
    rw [IH, Bool.and_assoc]

-- `Char.ofNat n` reads back as `n` or as `0` (the invalid-scalar fallback); neither is 10 or 13 once `48 ≤ n`.
-- This is what lets the four no-newline lemmas keep their unconditional statements (divergences).
private theorem ofNat_toNat_cases : ∀ n : Nat, (Char.ofNat n).toNat = n ∨ (Char.ofNat n).toNat = 0 := by
  intro n
  unfold Char.ofNat
  cases Decidable.em (Nat.isValidChar n) with
  | inl h => rw [dif_pos h]; exact Or.inl rfl
  | inr h => rw [dif_neg h]; exact Or.inr rfl

private theorem ofNat_not_nl_cr : ∀ n : Nat, 48 ≤ n → byte_not_nl_cr (Char.ofNat n) = true := by
  intro n Hn
  unfold byte_not_nl_cr
  cases ofNat_toNat_cases n with
  | inl h =>
    rw [h, decide_eq_false (fun e => absurd (e ▸ Hn) (by decide)),
      decide_eq_false (fun e => absurd (e ▸ Hn) (by decide))]
    rfl
  | inr h =>
    rw [h]
    rfl

private theorem hex_digit_not_nl_cr_any : ∀ k, byte_not_nl_cr (hex_digit k) = true := by
  intro k
  unfold hex_digit
  cases decide (k < 10) with
  | true => exact ofNat_not_nl_cr (48 + k) (Nat.le_add_right 48 k)
  | false => exact ofNat_not_nl_cr (87 + k) (Nat.le_trans (by decide) (Nat.le_add_right 87 k))

theorem hex_digit_not_nl_cr : ∀ k, k < 16 → byte_not_nl_cr (hex_digit k) = true :=
  fun k _ => hex_digit_not_nl_cr_any k

theorem hex_escape_no_nl_cr : ∀ c, str_no_nl_cr (hex_escape c) = true := by
  intro c
  show (byte_not_nl_cr bslash_c && (byte_not_nl_cr 'x'
    && (byte_not_nl_cr (hex_digit (c.toNat / 16)) && (byte_not_nl_cr (hex_digit (c.toNat % 16)) && true)))) = true
  rw [hex_digit_not_nl_cr_any, hex_digit_not_nl_cr_any]
  decide

theorem string_byte_no_nl_cr : ∀ c, str_no_nl_cr (string_byte c) = true := by
  intro c
  unfold string_byte
  dsimp only
  cases decide (c.toNat = 34) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 92) with
  | true => rfl
  | false =>
  cases E10 : decide (c.toNat = 10) with
  | true => rfl
  | false =>
  cases decide (c.toNat = 9) with
  | true => rfl
  | false =>
  cases E13 : decide (c.toNat = 13) with
  | true => rfl
  | false =>
  cases decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) with
  | true =>
    show (byte_not_nl_cr c && true) = true
    unfold byte_not_nl_cr
    rw [E10, E13]
    rfl
  | false => exact hex_escape_no_nl_cr c

theorem string_body_no_nl_cr : ∀ s, str_no_nl_cr (string_body s) = true := by
  intro s
  induction s with
  | nil => rfl
  | cons c s' IH =>
    show str_no_nl_cr (string_byte c ++ string_body s') = true
    rw [str_no_nl_cr_app, string_byte_no_nl_cr, IH]
    rfl

theorem string_literal_no_nl_cr : ∀ s, str_no_nl_cr (string_literal s) = true := by
  intro s
  show (byte_not_nl_cr dquote_c && str_no_nl_cr (string_body s ++ dquote_c :: [])) = true
  rw [str_no_nl_cr_app, string_body_no_nl_cr]
  decide

theorem string_literal_quotes : ∀ s,
    string_literal s = dquote_c :: (string_body s ++ dquote_c :: []) := fun _ => rfl

theorem byte_escape_quote : string_byte (Char.ofNat 34) = bslash_c :: dquote_c :: [] := by decide
theorem byte_escape_backslash : string_byte (Char.ofNat 92) = bslash_c :: bslash_c :: [] := by decide
theorem byte_escape_nl : string_byte (Char.ofNat 10) = bslash_c :: 'n' :: [] := by decide
theorem byte_escape_tab : string_byte (Char.ofNat 9) = bslash_c :: 't' :: [] := by decide
theorem byte_escape_cr : string_byte (Char.ofNat 13) = bslash_c :: 'r' :: [] := by decide
theorem byte_escape_nul : string_byte (Char.ofNat 0) = bslash_c :: 'x' :: '0' :: '0' :: [] := by decide
theorem byte_escape_del : string_byte (Char.ofNat 127) = bslash_c :: 'x' :: '7' :: 'f' :: [] := by decide
theorem byte_escape_80 : string_byte (Char.ofNat 128) = bslash_c :: 'x' :: '8' :: '0' :: [] := by decide
theorem byte_escape_ff : string_byte (Char.ofNat 255) = bslash_c :: 'x' :: 'f' :: 'f' :: [] := by decide
theorem literal_empty : string_literal (str! "") = dquote_c :: dquote_c :: [] := by decide
theorem literal_ascii : string_literal (str! "hi") = dquote_c :: 'h' :: 'i' :: dquote_c :: [] := by decide

/-! The render-time constant-status authority speaks the vocabulary Compilable.TypeResolution owns. -/
def digit_value (c : Char) : Option Nat :=
  let n := c.toNat
  bif decide (48 ≤ n) && decide (n ≤ 57) then some (n - 48) else none

def head_not_digit (s : Str) : Prop :=
  match s with | [] => True | c :: _ => digit_value c = none

def read_nat : Str → Int → Int × Str
  | [], acc => (acc, [])
  | c :: s', acc =>
      match digit_value c with
      | some d => read_nat s' (acc * 10 + (d : Int))
      | none => (acc, c :: s')

def read_signed_dec (s : Str) : Option (Int × Str) :=
  match s with
  | [] => none
  | c :: s' =>
      bif c == '-' then (let (m, r) := read_nat s' 0; some (-m, r))
      else bif c == '+' then (let (m, r) := read_nat s' 0; some (m, r))
      else (let (m, r) := read_nat (c :: s') 0; some (m, r))

def decode_decimal_body (s : Str) : Option Float.Constant :=
  match read_signed_dec s with
  | some (coeff, a :: b :: c :: r2) =>
      bif (a == '.') && ((b == '0') && (c == 'e')) then
        (match read_signed_dec r2 with
         | some (exp, []) => some (Float.decimal_to_constant coeff exp)
         | some (_, _ :: _) => none
         | none => none)
      else none
  | some (_, []) => none
  | some (_, [_]) => none
  | some (_, [_, _]) => none
  | none => none

def decode_decimal (s : Str) : Option Float.Constant :=
  match decode_decimal_body s with
  | some q => some q
  | none => bif decide (s = str! "0.0") then some Float.constant_zero else none

def str_all_digits : Str → Bool
  | [] => true
  | c :: s' => match digit_value c with | some _ => str_all_digits s' | none => false

theorem str_app_nil : ∀ s : Str, s ++ str! "" = s := by
  intro s
  induction s with
  | nil => rfl
  | cons c s' IH => show c :: (s' ++ []) = c :: s'; rw [IH]

theorem digit_value_digit : ∀ d, d < 10 → digit_value (Decimal.digit d) = some d := by decide

theorem str_all_digits_render_digits : ∀ ds acc,
    (∀ d ∈ ds, d < 10) → str_all_digits acc = true →
    str_all_digits (Decimal.render Decimal.digit ds acc) = true := by
  intro ds
  induction ds with
  | nil => intro _ _ Hacc; exact Hacc
  | cons a ds' IH =>
    intro acc Hall Hacc
    rw [digits_step]
    apply IH _ (fun d Hd => Hall d (List.Mem.tail _ Hd))
    show (match digit_value (Decimal.digit a) with | some _ => str_all_digits acc | none => false) = true
    rw [digit_value_digit a (Hall a (List.Mem.head _))]
    exact Hacc

theorem str_all_digits_print_Z_pos : ∀ p, 0 < p → str_all_digits (Decimal.positive p) = true := by
  intro p Hp
  unfold Decimal.positive
  exact str_all_digits_render_digits _ _ (fun d Hd => Decimal.positive_digits_bound 10 p (by decide) Hp d Hd) rfl

theorem str_all_digits_print_Z : ∀ z, 0 ≤ z → str_all_digits (Decimal.integer z) = true := by
  intro z H
  match z, H with
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), _ => exact str_all_digits_print_Z_pos (n + 1) (Nat.succ_pos n)
  | .negSucc _, H => exact absurd H (by omega)

-- The digit a `some` of `digit_value` reads is `ascii_digit` (Rocq: `injection Hc`).
private theorem digit_value_some : ∀ c d, digit_value c = some d → ascii_digit c = d := by
  intro c d
  unfold digit_value
  dsimp only
  cases decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57) with
  | true => intro h; exact Option.some.inj h
  | false => intro h; exact nomatch h

theorem read_nat_all_digits : ∀ s rest acc,
    str_all_digits s = true → head_not_digit rest → read_nat (s ++ rest) acc = (dval s acc, rest) := by
  intro s
  induction s with
  | nil =>
    intro rest acc _ Hrest
    cases rest with
    | nil => rfl
    | cons rc rr =>
      show (match digit_value rc with
            | some d => read_nat rr (acc * 10 + (d : Int)) | none => (acc, rc :: rr)) = (acc, rc :: rr)
      have Hrest' : digit_value rc = none := Hrest
      rw [Hrest']
  | cons c s' IH =>
    intro rest acc Hdig Hrest
    have Hdig' : (match digit_value c with | some _ => str_all_digits s' | none => false) = true := Hdig
    cases Hc : digit_value c with
    | none => rw [Hc] at Hdig'; exact nomatch Hdig'
    | some d =>
      rw [Hc] at Hdig'
      show (match digit_value c with
            | some d => read_nat (s' ++ rest) (acc * 10 + (d : Int)) | none => (acc, c :: (s' ++ rest)))
        = (dval s' (acc * 10 + (ascii_digit c : Int)), rest)
      rw [Hc]
      dsimp only
      rw [IH rest _ Hdig' Hrest, digit_value_some c d Hc]

theorem char_digit_not : ∀ c d,
    digit_value c = some d → (c == '-') = false ∧ (c == '+') = false := by
  intro c d Hc
  constructor
  · cases E : (c == '-') with
    | false => rfl
    | true =>
      have hc : c = '-' := of_decide_eq_true E
      subst hc
      have H : (none : Option Nat) = some d := Hc
      exact nomatch H
  · cases E : (c == '+') with
    | false => rfl
    | true =>
      have hc : c = '+' := of_decide_eq_true E
      subst hc
      have H : (none : Option Nat) = some d := Hc
      exact nomatch H

theorem integer_nonempty : ∀ z, 0 ≤ z → Decimal.integer z ≠ str! "" := by
  intro z H Hc
  match z, H, Hc with
  | .ofNat 0, _, Hc =>
    have H' : (str! "0" : Str) = [] := Hc
    exact nomatch H'
  | .ofNat (n + 1), _, Hc =>
    have Hf := integer_decimal_faithful (Int.ofNat (n + 1)) (Int.natCast_nonneg (n + 1))
    rw [Hc] at Hf
    have H' : Int.ofNat 0 = Int.ofNat (n + 1) := Hf
    exact Nat.succ_ne_zero n (Int.ofNat.inj H').symm
  | .negSucc _, H, _ => exact absurd H (by omega)

theorem read_signed_dec_all_digits : ∀ s rest,
    str_all_digits s = true → s ≠ str! "" → head_not_digit rest →
    read_signed_dec (s ++ rest) = some (dval0 s, rest) := by
  intro s rest Hdig Hne Hrest
  cases s with
  | nil => exact absurd rfl Hne
  | cons c s' =>
    have Hdig' : (match digit_value c with | some _ => str_all_digits s' | none => false) = true := Hdig
    cases Hc : digit_value c with
    | none => rw [Hc] at Hdig'; exact nomatch Hdig'
    | some d =>
      obtain ⟨Hnd, Hnp⟩ := char_digit_not c d Hc
      have E : read_nat (c :: (s' ++ rest)) 0 = (dval (c :: s') 0, rest) :=
        read_nat_all_digits (c :: s') rest 0 Hdig Hrest
      show read_signed_dec (c :: (s' ++ rest)) = some (dval (c :: s') 0, rest)
      unfold read_signed_dec
      dsimp only
      rw [Hnd, Hnp]
      dsimp only [cond]
      rw [E]

theorem read_signed_dec_sign : ∀ sgn mag rest,
    (sgn = '-' ∨ sgn = '+') → str_all_digits mag = true → head_not_digit rest →
    read_signed_dec (sgn :: (mag ++ rest))
    = some ((bif sgn == '-' then -(dval0 mag) else dval0 mag), rest) := by
  intro sgn mag rest Hsgn Hdig Hrest
  have E := read_nat_all_digits mag rest 0 Hdig Hrest
  cases Hsgn with
  | inl h =>
    subst h
    show (match read_nat (mag ++ rest) 0 with | (m, r) => some (-m, r)) = some (-(dval mag 0), rest)
    rw [E]
  | inr h =>
    subst h
    show (match read_nat (mag ++ rest) 0 with | (m, r) => some (m, r)) = some (dval mag 0, rest)
    rw [E]

theorem read_signed_dec_render_signed_Z : ∀ z rest, head_not_digit rest →
    read_signed_dec (signed_Z z ++ rest) = some (z, rest) := by
  intro z rest Hrest
  unfold signed_Z
  cases Hlt : decide (z < 0) with
  | true =>
    have Hlt' : z < 0 := of_decide_eq_true Hlt
    show read_signed_dec ('-' :: (Decimal.integer (-z) ++ rest)) = some (z, rest)
    rw [read_signed_dec_sign '-' _ rest (Or.inl rfl) (str_all_digits_print_Z (-z) (by omega)) Hrest]
    show some (-(dval0 (Decimal.integer (-z))), rest) = some (z, rest)
    rw [integer_decimal_faithful (-z) (by omega), Int.neg_neg]
  | false =>
    have Hge : 0 ≤ z := by have := of_decide_eq_false Hlt; omega
    show read_signed_dec (Decimal.integer z ++ rest) = some (z, rest)
    rw [read_signed_dec_all_digits _ rest (str_all_digits_print_Z z Hge) (integer_nonempty z Hge) Hrest,
      integer_decimal_faithful z Hge]

theorem read_signed_dec_render_signed_exp : ∀ z, read_signed_dec (signed_exp z) = some (z, str! "") := by
  intro z
  unfold signed_exp
  cases Hlt : decide (z < 0) with
  | true =>
    have Hlt' : z < 0 := of_decide_eq_true Hlt
    show read_signed_dec ('-' :: Decimal.integer (-z)) = some (z, [])
    rw [← str_app_nil (Decimal.integer (-z)),
      read_signed_dec_sign '-' _ (str! "") (Or.inl rfl) (str_all_digits_print_Z (-z) (by omega)) True.intro]
    show some (-(dval0 (Decimal.integer (-z))), []) = some (z, [])
    rw [integer_decimal_faithful (-z) (by omega), Int.neg_neg]
  | false =>
    have Hge : 0 ≤ z := by have := of_decide_eq_false Hlt; omega
    show read_signed_dec ('+' :: Decimal.integer z) = some (z, [])
    rw [← str_app_nil (Decimal.integer z),
      read_signed_dec_sign '+' _ (str! "") (Or.inr rfl) (str_all_digits_print_Z z Hge) True.intro]
    show some (dval0 (Decimal.integer z), []) = some (z, [])
    rw [integer_decimal_faithful z Hge]

theorem head_not_digit_dot0e : ∀ s, head_not_digit (str! ".0e" ++ s) := fun _ => rfl

/-- Without this shape guard the total prefix reader would let a float or `true` also denote an integer. -/
def go_int_lit (s : Str) : Bool :=
  match s with
  | [] => false
  | c :: s' =>
      bif c == '-'
      then (match s' with | [] => false | d :: t => str_all_digits (d :: t))
      else (match digit_value c with | some _ => str_all_digits s' | none => false)

theorem go_int_lit_all_digits_nonempty : ∀ s,
    str_all_digits s = true → s ≠ str! "" → go_int_lit s = true := by
  intro s Hdig Hne
  cases s with
  | nil => exact absurd rfl Hne
  | cons c s' =>
    have Hdig' : (match digit_value c with | some _ => str_all_digits s' | none => false) = true := Hdig
    cases Hc : digit_value c with
    | none => rw [Hc] at Hdig'; exact nomatch Hdig'
    | some d =>
      unfold go_int_lit
      dsimp only
      rw [(char_digit_not c d Hc).1]
      dsimp only [cond]
      exact Hdig'

theorem go_int_lit_neg : ∀ s,
    str_all_digits s = true → s ≠ str! "" → go_int_lit ('-' :: s) = true := by
  intro s Hdig Hne
  cases s with
  | nil => exact absurd rfl Hne
  | cons c s' => exact Hdig

theorem go_int_lit_integer_literal : ∀ n : Nat, go_int_lit (Decimal.integer (n : Int)) = true :=
  fun n => go_int_lit_all_digits_nonempty _ (str_all_digits_print_Z _ (Int.natCast_nonneg n))
    (integer_nonempty _ (Int.natCast_nonneg n))

theorem go_int_lit_negated_integer_literal : ∀ n : Nat,
    go_int_lit ('-' :: Decimal.integer (n : Int)) = true :=
  fun n => go_int_lit_neg _ (str_all_digits_print_Z _ (Int.natCast_nonneg n))
    (integer_nonempty _ (Int.natCast_nonneg n))

-- The `<coeff>.0e` shape of `decode_decimal_body`, once the coefficient has been read.
private theorem decode_decimal_body_shape : ∀ coeff r2 s,
    read_signed_dec s = some (coeff, '.' :: '0' :: 'e' :: r2) →
    decode_decimal_body s
    = match read_signed_dec r2 with
      | some (exp, []) => some (Float.decimal_to_constant coeff exp)
      | some (_, _ :: _) => none
      | none => none := by
  intro coeff r2 s H
  unfold decode_decimal_body
  rw [H]
  exact rfl

theorem decode_render_decimal : ∀ d, decode_decimal (decimal d) = some (Float.decimal_value d) := by
  intro d
  unfold decimal
  cases Hc0 : decide (Float.coefficient d = 0) with
  | true =>
    have Hc := of_decide_eq_true Hc0
    rw [Float.decimal_zero_unique d Hc]
    rfl
  | false =>
    have Hbody : decode_decimal_body (signed_Z (Float.coefficient d) ++ str! ".0e" ++ signed_exp (Float.exponent d))
        = some (Float.decimal_to_constant (Float.coefficient d) (Float.exponent d)) := by
      rw [← str_app_assoc]
      show decode_decimal_body (signed_Z (Float.coefficient d) ++ ('.' :: '0' :: 'e' :: signed_exp (Float.exponent d)))
        = _
      rw [decode_decimal_body_shape _ _ _
          (read_signed_dec_render_signed_Z (Float.coefficient d) ('.' :: '0' :: 'e' :: signed_exp (Float.exponent d))
            (head_not_digit_dot0e _)),
        read_signed_dec_render_signed_exp]
    show decode_decimal (signed_Z (Float.coefficient d) ++ str! ".0e" ++ signed_exp (Float.exponent d))
      = some (Float.decimal_value d)
    unfold decode_decimal
    rw [Hbody]
    exact rfl

private theorem digit_ne_minus : ∀ a, a < 10 → (Decimal.digit a == '-') = false := by decide

theorem positive_head_not_minus : ∀ p, 0 < p →
    match Decimal.positive p with | c :: _ => (c == '-') = false | [] => False := by
  intro p Hp
  unfold Decimal.positive
  rcases List.eq_nil_or_concat (Decimal.positive_digits 10 p) with Hnil | ⟨init, a, Ha⟩
  · exact absurd Hnil (Decimal.positive_digits_nonnil 10 p Hp)
  · rw [concat_eq_append] at Ha
    have Ha10 : a < 10 :=
      Decimal.positive_digits_bound 10 p (by decide) Hp a (by rw [Ha]; exact mem_concat a init)
    rw [Ha, digits_snoc]
    exact digit_ne_minus a Ha10

theorem read_go_int_nonneg : ∀ z, 0 ≤ z → read_go_int (Decimal.integer z) = dval0 (Decimal.integer z) := by
  intro z H
  match z, H with
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), _ =>
    have Hh := positive_head_not_minus (n + 1) (Nat.succ_pos n)
    show read_go_int (Decimal.positive (n + 1)) = dval0 (Decimal.positive (n + 1))
    revert Hh
    cases Decimal.positive (n + 1) with
    | nil => intro Hh; exact Hh.elim
    | cons c s' =>
      intro Hh
      have Hh' : (c == '-') = false := Hh
      show (bif c == '-' then -(dval0 s') else dval0 (c :: s')) = dval0 (c :: s')
      rw [Hh']
      rfl
  | .negSucc _, H => exact absurd H (by omega)

theorem read_go_int_integer_literal : ∀ n : Nat,
    read_go_int (render_expr (LiteralExpr (Syntax.IntegerLiteral n))) = (n : Int) := by
  intro n
  show read_go_int (Decimal.integer (n : Int)) = (n : Int)
  rw [read_go_int_nonneg _ (Int.natCast_nonneg n)]
  exact integer_decimal_faithful _ (Int.natCast_nonneg n)

theorem read_go_int_negated_integer_literal : ∀ n : Nat,
    read_go_int (render_expr (Unary Syntax.UnaryMinus (LiteralExpr (Syntax.IntegerLiteral n))))
    = -(n : Int) := by
  intro n
  show -(dval0 (Decimal.integer (n : Int))) = -(n : Int)
  rw [integer_decimal_faithful _ (Int.natCast_nonneg n)]

def ilit (n : Nat) : Expr := LiteralExpr (Syntax.IntegerLiteral n)
def flit (c e : Int) (w : Float.decimal_wfb c e = true) (nn : decide (0 ≤ c) = true) : Expr :=
  LiteralExpr (Syntax.FloatLiteral (Float.MakeNonNegDecimal (Float.MakeDecimal c e w) nn))
def cplx (re im : Expr) : Expr :=
  Application (Name (Names.predeclared_ordinary Names.PredeclaredName.PComplex)) [re, im]

/-- A bare integer stays untyped however large, which is why `uint64(2^63)` is valid. -/
theorem repair_bare_render : render_expr (ilit 9223372036854775808) = str! "9223372036854775808" := by
  decide +kernel

theorem float_1p5   : render_expr (flit 15 (-1) rfl rfl) = str! "15.0e-1" := by decide +kernel
theorem float_zero  : render_expr (flit 0 0 rfl rfl) = str! "0.0" := by decide
theorem float_1e6   : render_expr (flit 1 6 rfl rfl) = str! "1.0e+6" := by decide +kernel
theorem float_neg   : render_expr (Unary Syntax.UnaryMinus (flit 15 (-1) rfl rfl)) = str! "-15.0e-1" := by
  decide +kernel

theorem cplx_lit  : render_expr (cplx (flit 15 (-1) rfl rfl)
                                      (Unary Syntax.UnaryMinus (flit 25 (-1) rfl rfl)))
    = str! "complex(15.0e-1, -25.0e-1)" := by decide +kernel
theorem cplx_zero : render_expr (cplx (flit 0 0 rfl rfl) (flit 0 0 rfl rfl))
    = str! "complex(0.0, 0.0)" := by decide

end Fido.Render
