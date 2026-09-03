-- Port of Names.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  * `ascii` is `Char` (README): `nat_of_ascii` is `Char.toNat`, whose range is the Unicode scalars
    (`< 0x110000`), not `< 256`.  No proof here relies on the 8-bit bound — `is_ascii_c` compares against
    128 either way, `alpha_ascii`/`digit_ascii` bound the code by the alphabet ranges, and
    `underscore_ascii` evaluates `'_'` — so no bound is added anywhere.
  * The stdlib boolean tests are the mapped types' decision procedures: `String.eqb`/`Ascii.eqb` are
    `decide (_ = _)` on `Str`/`Char`, `Nat.leb`/`Nat.ltb` are `decide (_ ≤ _)`/`decide (_ < _)`,
    `Bool.bool_dec _ false` is `if h : _ = false`; `existsb`/`find`/`In`/`NoDup` are
    `List.any`/`List.find?`/`∈`/`List.Nodup`.
  * `{a = b} + {a <> b}` is `Decidable (a = b)`: `predeclared_eq_dec` is the `deriving DecidableEq` instance
    (Lean's `decide equality`), and `predeclared_eqb` matches on it as Rocq's `if` on a sumbool does.
  * `UIP_dec Bool.bool_dec` is definitional proof irrelevance (`identifier_ok_irrel` is `rfl`).
  * Rocq's named `Example`s are `theorem`s (a Lean `example` is anonymous, and `blank_not_ordinary` cites
    `blank_is_identifier`).
-/

namespace Fido.Names

def is_alpha (c : Char) : Bool :=
  let n := c.toNat
  (decide (65 ≤ n) && decide (n ≤ 90)) || (decide (97 ≤ n) && decide (n ≤ 122))
def is_digit (c : Char) : Bool :=
  let n := c.toNat
  decide (48 ≤ n) && decide (n ≤ 57)
def is_underscore (c : Char) : Bool := decide (c = '_')

def identifier_start (c : Char) : Bool := is_alpha c || is_underscore c
def identifier_cont  (c : Char) : Bool := is_alpha c || is_digit c || is_underscore c

def identifier_rest_ok : Str → Bool
  | [] => true
  | c :: s' => identifier_cont c && identifier_rest_ok s'

def identifier_shape_ok (s : Str) : Bool :=
  match s with
  | [] => false
  | c :: s' => identifier_start c && identifier_rest_ok s'

/-- the pinned Go keywords (Go spec) — none may inhabit `Identifier`. -/
def go_keywords : List Str :=
  [ str! "break", str! "case", str! "chan", str! "const", str! "continue", str! "default", str! "defer",
    str! "else", str! "fallthrough", str! "for", str! "func", str! "go", str! "goto", str! "if",
    str! "import", str! "interface", str! "map", str! "package", str! "range", str! "return",
    str! "select", str! "struct", str! "switch", str! "type", str! "var" ]
def is_keyword (s : Str) : Bool := go_keywords.any (fun k => decide (s = k))

def identifier_ok (s : Str) : Bool := identifier_shape_ok s && !(is_keyword s)

-- `genInjectivity false`: the auto-generated `injEq` is the one `propext` use in the module; nothing here
-- needs it, and Rocq's `Record` generates no such theorem.
set_option genInjectivity false in
/-- A source identifier carries its own validity proof, so no unchecked string can construct one. -/
structure Identifier : Type where
  MakeIdentifier ::
  spelling : Str
  valid : identifier_ok spelling = true

open Identifier

theorem identifier_ok_irrel : ∀ s (p q : identifier_ok s = true), p = q := fun _ _ _ => rfl

theorem identifier_equal : ∀ a b, spelling a = spelling b → a = b := by
  intro ⟨sa, _⟩ ⟨sb, _⟩ H
  have H' : sa = sb := H
  subst H'
  rfl

def equalb (a b : Identifier) : Bool := decide (spelling a = spelling b)
theorem equalb_spec : ∀ a b, equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H; exact identifier_equal a b (of_decide_eq_true H)
  · intro H; subst H; exact decide_eq_true rfl

def render_identifier (i : Identifier) : Str := spelling i


def is_ascii_c (c : Char) : Bool := decide (c.toNat < 128)
def str_ascii : Str → Bool
  | [] => true
  | c :: s' => is_ascii_c c && str_ascii s'

-- Rocq: `Bool.andb_true_iff` / `Bool.orb_true_iff`, one direction each, by cases (no `propext`).
private theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h
private theorem bor_true : ∀ {a b : Bool}, (a || b) = true → a = true ∨ b = true
  | true, _, _ => .inl rfl
  | false, true, _ => .inr rfl
  | false, false, h => nomatch h

-- Rocq: `lia`.  Each range's upper bound is a literal below 128, so `Nat.lt_of_le_of_lt` with the
-- `decide`d constant fact is the whole argument (`omega` would put `propext` and `Quot.sound` in the closure).
theorem alpha_ascii : ∀ c, is_alpha c = true → is_ascii_c c = true := by
  intro c H
  apply decide_eq_true
  rcases bor_true H with H | H
  · exact Nat.lt_of_le_of_lt (of_decide_eq_true (band_true H).2) (by decide)
  · exact Nat.lt_of_le_of_lt (of_decide_eq_true (band_true H).2) (by decide)
theorem digit_ascii : ∀ c, is_digit c = true → is_ascii_c c = true := by
  intro c H
  apply decide_eq_true
  exact Nat.lt_of_le_of_lt (of_decide_eq_true (band_true H).2) (by decide)
theorem underscore_ascii : ∀ c, is_underscore c = true → is_ascii_c c = true := by
  intro c H
  cases of_decide_eq_true H
  decide

theorem identifier_start_ascii : ∀ c, identifier_start c = true → is_ascii_c c = true := by
  intro c H
  rcases bor_true H with H | H
  · exact alpha_ascii c H
  · exact underscore_ascii c H
theorem identifier_cont_ascii : ∀ c, identifier_cont c = true → is_ascii_c c = true := by
  intro c H
  rcases bor_true H with H | H
  · rcases bor_true H with H | H
    · exact alpha_ascii c H
    · exact digit_ascii c H
  · exact underscore_ascii c H

theorem identifier_rest_ascii : ∀ s, identifier_rest_ok s = true → str_ascii s = true := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s IH =>
    intro H
    obtain ⟨Hc, Hr⟩ := band_true H
    show (is_ascii_c c && str_ascii s) = true
    rw [identifier_cont_ascii c Hc, IH Hr]; rfl

theorem identifier_ascii : ∀ i, str_ascii (render_identifier i) = true := by
  intro ⟨s, Hs⟩
  show str_ascii s = true
  obtain ⟨Hshape, _⟩ := band_true Hs
  cases s with
  | nil => exact nomatch Hshape
  | cons c s' =>
    obtain ⟨Hst, Hr⟩ := band_true Hshape
    show (is_ascii_c c && str_ascii s') = true
    rw [identifier_start_ascii c Hst, identifier_rest_ascii s' Hr]; rfl

/-- An ordinary identifier is exactly a nonblank one; blank is reserved for a later `Syntax.BindingName`. -/
def is_blank (s : Str) : Bool := decide (s = str! "_")

theorem is_blank_true : ∀ s, is_blank s = true ↔ s = str! "_" := by
  intro s; exact ⟨of_decide_eq_true, decide_eq_true⟩
theorem is_blank_false : ∀ s, is_blank s = false ↔ s ≠ str! "_" := by
  intro s
  constructor
  · intro H Heq
    subst Heq
    have Ht : is_blank (str! "_") = true := rfl
    exact Bool.noConfusion (Ht.symm.trans H)
  · intro H; exact decide_eq_false H

set_option genInjectivity false in
/-- The ordinary object retains the exact `Identifier`; it never copies the spelling and rebuilds one. -/
structure OrdinaryIdentifier : Type where
  MakeOrdinary ::
  ordinary_id : Identifier
  ordinary_ok : is_blank (spelling ordinary_id) = false

open OrdinaryIdentifier

def ordinary_spelling (o : OrdinaryIdentifier) : Str := spelling (ordinary_id o)
def render_ordinary (o : OrdinaryIdentifier) : Str := render_identifier (ordinary_id o)

/-- One total smart constructor: it succeeds on exactly the nonblank identifiers. -/
def ordinary_of (i : Identifier) : Option OrdinaryIdentifier :=
  if H : is_blank (spelling i) = false then some (MakeOrdinary i H) else none

theorem ordinary_nonblank : ∀ o : OrdinaryIdentifier, spelling (ordinary_id o) ≠ str! "_" := by
  intro ⟨_, H⟩
  exact (is_blank_false _).1 H

theorem ordinary_of_some_iff : ∀ i, (∃ o, ordinary_of i = some o) ↔ is_blank (spelling i) = false := by
  intro i
  unfold ordinary_of
  obtain h | h := Decidable.em (is_blank (spelling i) = false)
  · rw [dif_pos h]
    exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
  · rw [dif_neg h]
    exact ⟨fun ⟨_, Ho⟩ => (nomatch Ho), fun hf => absurd hf h⟩

theorem ordinary_of_id : ∀ i o, ordinary_of i = some o → ordinary_id o = i := by
  intro i o Ho
  unfold ordinary_of at Ho
  obtain h | h := Decidable.em (is_blank (spelling i) = false)
  · rw [dif_pos h] at Ho
    cases Ho
    rfl
  · rw [dif_neg h] at Ho
    exact nomatch Ho

theorem ordinary_of_success :
    ∀ i, spelling i ≠ str! "_" → ∃ o, ordinary_of i = some o ∧ ordinary_id o = i := by
  intro i Hne
  have Hb : is_blank (spelling i) = false := (is_blank_false _).2 Hne
  exact ⟨MakeOrdinary i Hb, dif_pos Hb, rfl⟩

theorem ordinary_of_fail : ∀ i, spelling i = str! "_" → ordinary_of i = none := by
  intro i He
  have Hb : is_blank (spelling i) = true := (is_blank_true _).2 He
  exact dif_neg (fun e => Bool.noConfusion (Hb.symm.trans e))

theorem ordinary_equal : ∀ a b, ordinary_id a = ordinary_id b → a = b := by
  intro ⟨ia, _⟩ ⟨ib, _⟩ H
  have H' : ia = ib := H
  subst H'
  rfl
theorem ordinary_equal_spelling : ∀ a b, spelling (ordinary_id a) = spelling (ordinary_id b) → a = b := by
  intro a b H; exact ordinary_equal a b (identifier_equal _ _ H)

def ordinary_equalb (a b : OrdinaryIdentifier) : Bool := equalb (ordinary_id a) (ordinary_id b)
theorem ordinary_equalb_spec : ∀ a b, ordinary_equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H; exact ordinary_equal a b ((equalb_spec _ _).1 H)
  · intro H; subst H; exact (equalb_spec _ _).2 rfl

theorem render_ordinary_ascii : ∀ o, str_ascii (render_ordinary o) = true :=
  fun o => identifier_ascii (ordinary_id o)


/-- The complete pinned 44-identity predeclared catalog; membership confers identity only, never a meaning. -/
inductive PredeclaredName : Type
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError
  | PFloat32 | PFloat64 | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString
  | PUint | PUint8 | PUint16 | PUint32 | PUint64 | PUintptr
  | PTrue | PFalse | PIota | PNil
  | PAppend | PCap | PClear | PClose | PComplex | PCopy | PDelete | PImag | PLen
  | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal | PRecover
  deriving DecidableEq

open PredeclaredName

def predeclared_spelling (n : PredeclaredName) : Str :=
  match n with
  | PAny => str! "any" | PBool => str! "bool" | PByte => str! "byte" | PComparable => str! "comparable"
  | PComplex64 => str! "complex64" | PComplex128 => str! "complex128" | PError => str! "error"
  | PFloat32 => str! "float32" | PFloat64 => str! "float64"
  | PInt => str! "int" | PInt8 => str! "int8" | PInt16 => str! "int16" | PInt32 => str! "int32"
  | PInt64 => str! "int64"
  | PRune => str! "rune" | PString => str! "string"
  | PUint => str! "uint" | PUint8 => str! "uint8" | PUint16 => str! "uint16" | PUint32 => str! "uint32"
  | PUint64 => str! "uint64" | PUintptr => str! "uintptr"
  | PTrue => str! "true" | PFalse => str! "false" | PIota => str! "iota" | PNil => str! "nil"
  | PAppend => str! "append" | PCap => str! "cap" | PClear => str! "clear" | PClose => str! "close"
  | PComplex => str! "complex" | PCopy => str! "copy" | PDelete => str! "delete" | PImag => str! "imag"
  | PLen => str! "len" | PMake => str! "make" | PMax => str! "max" | PMin => str! "min" | PNew => str! "new"
  | PPanic => str! "panic" | PPrint => str! "print" | PPrintln => str! "println" | PReal => str! "real"
  | PRecover => str! "recover"

def all_predeclared : List PredeclaredName :=
  [ PAny, PBool, PByte, PComparable, PComplex64, PComplex128, PError,
    PFloat32, PFloat64, PInt, PInt8, PInt16, PInt32, PInt64, PRune, PString,
    PUint, PUint8, PUint16, PUint32, PUint64, PUintptr,
    PTrue, PFalse, PIota, PNil,
    PAppend, PCap, PClear, PClose, PComplex, PCopy, PDelete, PImag, PLen,
    PMake, PMax, PMin, PNew, PPanic, PPrint, PPrintln, PReal, PRecover ]

def predeclared_eq_dec : ∀ a b : PredeclaredName, Decidable (a = b) := inferInstance
def predeclared_eqb (a b : PredeclaredName) : Bool :=
  match predeclared_eq_dec a b with
  | isTrue _ => true
  | isFalse _ => false
theorem predeclared_eqb_spec : ∀ a b, predeclared_eqb a b = true ↔ a = b := by
  intro a b
  unfold predeclared_eqb
  cases predeclared_eq_dec a b with
  | isTrue h => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun e => (nomatch e), fun e => absurd e h⟩

/-- The one classifier from a source spelling to a full predeclared identity. -/
def classify_predeclared (s : Str) : Option PredeclaredName :=
  all_predeclared.find? (fun n => decide (s = predeclared_spelling n))

-- Rocq: `destruct n; reflexivity` / `vm_compute`.  The three 44-way evaluations below use `decide +kernel`:
-- one kernel evaluation, where plain `decide` pre-evaluates in the elaborator and the kernel re-checks
-- (0.17 s of this module's 1.4 s).
theorem classify_predeclared_roundtrip : ∀ n, classify_predeclared (predeclared_spelling n) = some n := by
  intro n; cases n <;> decide +kernel

-- Rocq: `find_some`, the `p a = true` half.  Core's `List.find?_some` is proved by `simp` and so depends on
-- `propext`; this one is the plain induction.
private theorem find_some {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a → p a = true
  | [], _, h => nomatch h
  | x :: xs, a, h => by
    revert h
    simp only [List.find?]
    cases hx : p x
    · exact fun h => find_some p xs a h
    · exact fun h => Option.some.inj h ▸ hx

theorem classify_predeclared_sound : ∀ s n, classify_predeclared s = some n → s = predeclared_spelling n := by
  intro s n H
  unfold classify_predeclared at H
  have Hb := find_some _ _ _ H
  exact of_decide_eq_true Hb

theorem predeclared_spelling_inj : ∀ a b, predeclared_spelling a = predeclared_spelling b → a = b := by
  intro a b H
  have Ha := classify_predeclared_roundtrip a
  rw [H, classify_predeclared_roundtrip] at Ha
  exact (Option.some.inj Ha).symm

theorem all_predeclared_complete : ∀ n, n ∈ all_predeclared := by
  intro n; unfold all_predeclared
  cases n <;> repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
theorem all_predeclared_nodup : List.Nodup all_predeclared := by decide +kernel

theorem predeclared_spelling_ok : ∀ n, identifier_ok (predeclared_spelling n) = true := by
  intro n; cases n <;> decide +kernel
theorem predeclared_nonblank : ∀ n, is_blank (predeclared_spelling n) = false := by
  intro n; cases n <;> decide

/-- Each identity has exactly one canonical `Identifier` and one canonical ordinary identifier. -/
def predeclared_identifier (n : PredeclaredName) : Identifier :=
  MakeIdentifier (predeclared_spelling n) (predeclared_spelling_ok n)
def predeclared_ordinary (n : PredeclaredName) : OrdinaryIdentifier :=
  MakeOrdinary (predeclared_identifier n) (predeclared_nonblank n)
theorem predeclared_ordinary_spelling :
    ∀ n, ordinary_spelling (predeclared_ordinary n) = predeclared_spelling n := fun _ => rfl

theorem predeclared_byte_neq_uint8 : PByte ≠ PUint8 := nofun
theorem predeclared_rune_neq_int32 : PRune ≠ PInt32 := nofun

/-- Adversarial controls: blank is an identifier yet never ordinary; catalog membership is exact. -/
theorem blank_is_identifier : identifier_ok (str! "_") = true := by decide
theorem blank_not_ordinary : ordinary_of (MakeIdentifier (str! "_") blank_is_identifier) = none := rfl
theorem keyword_type_not_ident : identifier_ok (str! "type") = false := by decide
theorem foo_not_predeclared : classify_predeclared (str! "foo") = none := by decide
theorem qualified_not_predeclared : classify_predeclared (str! "pkg.T") = none := by decide
theorem bool_in_catalog : classify_predeclared (str! "bool") = some PBool := by decide
theorem string_in_catalog : classify_predeclared (str! "string") = some PString := by decide
theorem uintptr_in_catalog : classify_predeclared (str! "uintptr") = some PUintptr := by decide
theorem any_in_catalog : classify_predeclared (str! "any") = some PAny := by decide
theorem error_in_catalog : classify_predeclared (str! "error") = some PError := by decide
theorem comparable_in_catalog : classify_predeclared (str! "comparable") = some PComparable := by decide

end Fido.Names
