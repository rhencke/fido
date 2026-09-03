-- Port of Compilable/TypeResolution.v (lean/README.md).
import Fido.Integer
import Fido.Float
import Fido.Complex
import Fido.Names

/-! divergences:
  * `float_constant_neg` builds a `Float.Constant`, which in the port carries one extra `Prop` field
    (`denominator_pos`, Float.lean: `positive` is `Nat` with `0 < n` carried); it passes the negated
    constant's own `Float.denominator_pos q` through unchanged.  `Zpos (Float.denominator q)` is the cast
    `(Float.denominator q : Int)`; `Z.rem` is `Int.tmod` and `Z.div` is `/` (`Int.ediv`, which agrees with
    `Z.div` on the positive divisor `constant_to_int` uses — Float.lean); `Z.eqb` / `Z.gcd … =? 1` are
    `decide` on the corresponding propositions, so `float_constant_neg_canonical` reads
    `decide (Int.gcd (- numerator q) (denominator q) = 1) = true`, the shape of `Float.canonical`.
  * `bool_true_dec`'s sumbool `{b = true} + {b = false}` is `PSum (b = true) (b = false)` (`⊕'`, as
    Machine.lean renders `+` over `Prop`s): `Decidable` would carry `¬ b = true` on the right, not `b = false`.
  * Catch-all `_` match arms are enumerated (Integer.lean): `form_equalb`'s twenty off-diagonal pairs,
    the `None`/`NotForm`/`false` arms of `int_value`, `float_value`, `complex_value`, `convert_constant`,
    `constant_representableb`, `constant_neg`, `constant_to_float`, `complex_of_constants`, and the
    twenty-four `NMNoFormMeaning` names of `predeclared_meaning`.
  * Integer.lean never opens `Integer.Kind` (its constructor `Int` shares its spelling with Lean's `Int`), so
    `Integer.Int` is written `Integer.Kind.Int`; `Float.F64` / `Complex.C128` are opened as in Complex.lean.
  * The three `Fail Definition` negative checks (a mismatched or out-of-range typed constant) are not
    declarations and have no positive counterpart; the indexed family and the `TCInt` proof field refuse
    them the same way (`TCInt Integer.Kind.Int8 128 rfl` has no proof of `representableb … = true`).
  * `Arguments Converted {target} _` (and `Overflows`, `NotForm`) is Lean's default — an inductive's
    parameter is implicit in its constructors — so it is not written.
  * Axiom closure (the audit's finding; no statement changes): `propext` and `Quot.sound` enter only through
    Float.lean's `Int.gcd` constants (`Float.constant_of_Z`, `Float.constant_zero`, `Float.TypedConstant`,
    `Float.round_typed_float`, and Complex.lean's `of_real`, `real_if_imaginary_zero`, `TypedConstant`,
    `round_typed` over them), so every constant here that mentions one inherits both: `TypedConstant` and
    everything over it (`typed_exact`, `typed_constant_intrinsic`, `ResolvedConstant` and its two projections,
    `ConversionResult`, `convert_constant`, `convert_total_exact`, `constant_representableb`,
    `ConstantRepresentable`, `representable_iff_converted`, `default_constant`), and `int_value`,
    `float_value`, `complex_value`, `constant_to_float`, `complex_of_constants`.  `TypeForm`, `form_equalb`
    and its two lemmas, `Constant`, `TypedFlag`, `ConstantInfo`, `constant_to_int`, `bool_true_dec`,
    `float_constant_neg_canonical`, `float_constant_neg`, `constant_neg`, `NameMeaning` and
    `predeclared_meaning` are axiom-free.  Nothing here reaches `Classical.choice`.
-/

namespace Fido.Compilable.TypeResolution
open Float.Kind (F32 F64)
open Complex.Kind (C64 C128)

/-! Pure structural form only: `TypeForm` is the shape a constant may take, never a nominal type identity. -/

-- Rocq generates no injectivity or size lemmas (Float.lean); each auto-generated `injEq` is a `propext` user.
set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive TypeForm : Type
  | BoolForm
  | IntegerForm : Integer.Kind → TypeForm
  | FloatForm   : Float.Kind → TypeForm
  | ComplexForm : Complex.Kind → TypeForm
  | StringForm

open TypeForm

def form_equalb (a b : TypeForm) : Bool :=
  match a, b with
  | BoolForm, BoolForm => true
  | IntegerForm k1, IntegerForm k2 => Integer.equalb k1 k2
  | FloatForm k1, FloatForm k2 => Float.kind_equalb k1 k2
  | ComplexForm k1, ComplexForm k2 => Complex.kind_equalb k1 k2
  | StringForm, StringForm => true
  | BoolForm, IntegerForm _ | BoolForm, FloatForm _ | BoolForm, ComplexForm _ | BoolForm, StringForm
  | IntegerForm _, BoolForm | IntegerForm _, FloatForm _ | IntegerForm _, ComplexForm _ | IntegerForm _, StringForm
  | FloatForm _, BoolForm | FloatForm _, IntegerForm _ | FloatForm _, ComplexForm _ | FloatForm _, StringForm
  | ComplexForm _, BoolForm | ComplexForm _, IntegerForm _ | ComplexForm _, FloatForm _ | ComplexForm _, StringForm
  | StringForm, BoolForm | StringForm, IntegerForm _ | StringForm, FloatForm _ | StringForm, ComplexForm _ => false

theorem form_equalb_spec : ∀ a b, form_equalb a b = true ↔ a = b := by
  intro a b
  cases a <;> cases b
  case BoolForm.BoolForm => exact ⟨fun _ => rfl, fun _ => rfl⟩
  case StringForm.StringForm => exact ⟨fun _ => rfl, fun _ => rfl⟩
  case IntegerForm.IntegerForm k1 k2 =>
    constructor
    · intro h; exact congrArg IntegerForm ((Integer.equalb_spec k1 k2).1 h)
    · intro h; cases h; exact (Integer.equalb_spec k1 k1).2 rfl
  case FloatForm.FloatForm k1 k2 =>
    constructor
    · intro h; exact congrArg FloatForm ((Float.kind_equalb_spec k1 k2).1 h)
    · intro h; cases h; exact (Float.kind_equalb_spec k1 k1).2 rfl
  case ComplexForm.ComplexForm k1 k2 =>
    constructor
    · intro h; exact congrArg ComplexForm ((Complex.kind_equalb_spec k1 k2).1 h)
    · intro h; cases h; exact (Complex.kind_equalb_spec k1 k1).2 rfl
  all_goals exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- Distinct forms are separated by the decision procedure: form carries no identity that would merge them. -/
theorem form_identity_separation : ∀ a b, a ≠ b ↔ form_equalb a b = false := by
  intro a b
  constructor
  · intro Hne
    cases E : form_equalb a b with
    | true => exact absurd ((form_equalb_spec a b).1 E) Hne
    | false => rfl
  · intro E Heq
    subst Heq
    have H : form_equalb a a = true := (form_equalb_spec a a).2 rfl
    exact Bool.noConfusion (H.symm.trans E)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact folded constant value; never a nominal type. -/
inductive Constant : Type
  | CInt     : Int → Constant
  | CFloat   : Float.Constant → Constant
  | CComplex : Complex.Constant → Constant
  | CString  : Str → Constant
  | CBool    : Bool → Constant

open Constant

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A typed constant cannot exist without the evidence its form requires, so an out-of-range one has no
    value. -/
inductive TypedConstant : TypeForm → Type
  | TCBool    : Bool → TypedConstant BoolForm
  | TCInt     : ∀ (k : Integer.Kind) (z : Int), Integer.representableb k z = true → TypedConstant (IntegerForm k)
  | TCFloat   : ∀ (k : Float.Kind), Float.TypedConstant k → TypedConstant (FloatForm k)
  | TCComplex : ∀ (k : Complex.Kind), Complex.TypedConstant k → TypedConstant (ComplexForm k)
  | TCString  : Str → TypedConstant StringForm

open TypedConstant

/-- Forget the form, keep the exact constant; reads stored data and never re-rounds. -/
def typed_exact {t : TypeForm} (tc : TypedConstant t) : Constant :=
  match tc with
  | TCBool b       => CBool b
  | TCInt _ z _    => CInt z
  | TCFloat _ v    => CFloat (Float.«exact» v)
  | TCComplex _ v  => CComplex (Complex.typed_exact v)
  | TCString s     => CString s

/-- A typed constant's exact value has exactly the shape its form dictates; integers carry their range
    proof. -/
theorem typed_constant_intrinsic : ∀ t (tc : TypedConstant t),
    (match t with
     | BoolForm      => fun c => ∃ b, typed_exact c = CBool b
     | IntegerForm k => fun c => ∃ z, typed_exact c = CInt z ∧ Integer.representableb k z = true
     | FloatForm _   => fun c => ∃ q, typed_exact c = CFloat q
     | ComplexForm _ => fun c => ∃ cc, typed_exact c = CComplex cc
     | StringForm    => fun c => ∃ s, typed_exact c = CString s
     : TypedConstant t → Prop) tc := by
  intro t tc
  cases tc with
  | TCBool b => exact ⟨b, rfl⟩
  | TCInt k z H => exact ⟨z, rfl, H⟩
  | TCFloat k v => exact ⟨Float.«exact» v, rfl⟩
  | TCComplex k v => exact ⟨Complex.typed_exact v, rfl⟩
  | TCString s => exact ⟨s, rfl⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive TypedFlag : Type
  | Untyped
  | ExplicitlyTyped : TypeForm → TypedFlag

open TypedFlag

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure ConstantInfo : Type where
  mk_cinfo ::
  ci_const : Constant
  ci_typed : TypedFlag

export ConstantInfo (mk_cinfo ci_const ci_typed)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure ResolvedConstant : Type where
  mk_rc ::
  rc_form  : TypeForm
  rc_value : TypedConstant rc_form

export ResolvedConstant (mk_rc rc_form rc_value)

def resolved_constant_form (rc : ResolvedConstant) : TypeForm := rc_form rc
def resolved_constant_exact (rc : ResolvedConstant) : Constant := typed_exact (rc_value rc)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Conversion is total with three exact outcomes: a target-form value, an out-of-range value, or not the
    target form. -/
inductive ConversionResult (target : TypeForm) : Type
  | Converted : TypedConstant target → ConversionResult target
  | Overflows : Constant → ConversionResult target
  | NotForm   : Constant → ConversionResult target

open ConversionResult

/-- The exact integer a constant denotes, when it denotes one; the sole float/complex-to-integer bridge. -/
def constant_to_int (q : Float.Constant) : Option Int :=
  if Int.tmod (Float.numerator q) (Float.denominator q : Int) = 0
  then some (Float.numerator q / (Float.denominator q : Int)) else none

def int_value (c : Constant) : Option Int :=
  match c with
  | CInt z     => some z
  | CFloat q   => constant_to_int q
  | CComplex cc => match Complex.real_if_imaginary_zero cc with | some q => constant_to_int q | none => none
  | CString _  => none
  | CBool _    => none
def float_value (c : Constant) : Option Float.Constant :=
  match c with
  | CInt z     => some (Float.constant_of_Z z)
  | CFloat q   => some q
  | CComplex cc => Complex.real_if_imaginary_zero cc
  | CString _  => none
  | CBool _    => none
def complex_value (c : Constant) : Option Complex.Constant :=
  match c with
  | CInt z     => some (Complex.of_real (Float.constant_of_Z z))
  | CFloat q   => some (Complex.of_real q)
  | CComplex cc => some cc
  | CString _  => none
  | CBool _    => none

/-- A decidable guard carrying its own proof, so the integer branch needs no dependent convoy. -/
def bool_true_dec (b : Bool) : (b = true) ⊕' (b = false) :=
  match b with | true => .inl rfl | false => .inr rfl

def convert_constant (target : TypeForm) (ci : ConstantInfo) : ConversionResult target :=
  let c := ci_const ci
  match target with
  | BoolForm     => match c with
                    | CBool b => Converted (TCBool b)
                    | CInt _ => NotForm c | CFloat _ => NotForm c | CComplex _ => NotForm c | CString _ => NotForm c
  | StringForm   => match c with
                    | CString s => Converted (TCString s)
                    | CInt _ => NotForm c | CFloat _ => NotForm c | CComplex _ => NotForm c | CBool _ => NotForm c
  | IntegerForm k =>
      match int_value c with
      | some z => match bool_true_dec (Integer.representableb k z) with
                  | .inl H => Converted (TCInt k z H)
                  | .inr _ => Overflows c
      | none => NotForm c
  | FloatForm k =>
      match float_value c with
      | some q => match Float.round_typed_float k q with
                  | some v => Converted (TCFloat k v)
                  | none   => Overflows c
      | none => NotForm c
  | ComplexForm k =>
      match complex_value c with
      | some cc => match Complex.round_typed k cc with
                   | some v => Converted (TCComplex k v)
                   | none   => Overflows c
      | none => NotForm c

/-- A failed conversion carries the exact offending constant, so overflow diagnostics name the real value. -/
theorem convert_total_exact : ∀ target ci,
    (∀ c, convert_constant target ci = Overflows c → c = ci_const ci)
    ∧ (∀ c, convert_constant target ci = NotForm c → c = ci_const ci) := by
  intro target ci
  cases ci with | mk_cinfo c0 f =>
  unfold convert_constant
  cases target <;> dsimp only
  case BoolForm =>
    cases c0 <;> dsimp only <;> exact ⟨fun c H => (nomatch H), fun c H => by cases H <;> rfl⟩
  case StringForm =>
    cases c0 <;> dsimp only <;> exact ⟨fun c H => (nomatch H), fun c H => by cases H <;> rfl⟩
  case IntegerForm k =>
    cases int_value c0 <;> dsimp only
    case none => exact ⟨fun c H => (nomatch H), fun c H => by cases H; rfl⟩
    case some z =>
      cases bool_true_dec (Integer.representableb k z) <;> dsimp only
      case inl H => exact ⟨fun c H => (nomatch H), fun c H => (nomatch H)⟩
      case inr H => exact ⟨fun c H => by cases H; rfl, fun c H => (nomatch H)⟩
  case FloatForm k =>
    cases float_value c0 <;> dsimp only
    case none => exact ⟨fun c H => (nomatch H), fun c H => by cases H; rfl⟩
    case some q =>
      cases Float.round_typed_float k q <;> dsimp only
      case some v => exact ⟨fun c H => (nomatch H), fun c H => (nomatch H)⟩
      case none => exact ⟨fun c H => by cases H; rfl, fun c H => (nomatch H)⟩
  case ComplexForm k =>
    cases complex_value c0 <;> dsimp only
    case none => exact ⟨fun c H => (nomatch H), fun c H => by cases H; rfl⟩
    case some cc =>
      cases Complex.round_typed k cc <;> dsimp only
      case some v => exact ⟨fun c H => (nomatch H), fun c H => (nomatch H)⟩
      case none => exact ⟨fun c H => by cases H; rfl, fun c H => (nomatch H)⟩

def constant_representableb (target : TypeForm) (c : Constant) : Bool :=
  match convert_constant target (mk_cinfo c Untyped) with
  | Converted _ => true
  | Overflows _ => false
  | NotForm _ => false

def ConstantRepresentable (target : TypeForm) (c : Constant) : Prop :=
  constant_representableb target c = true

theorem representable_iff_converted : ∀ target c,
    ConstantRepresentable target c ↔ ∃ tc, convert_constant target (mk_cinfo c Untyped) = Converted tc := by
  intro target c
  unfold ConstantRepresentable constant_representableb
  cases E : convert_constant target (mk_cinfo c Untyped) with
  | Converted tc => exact ⟨fun _ => ⟨tc, rfl⟩, fun _ => rfl⟩
  | Overflows _ => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩
  | NotForm _ => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

-- Rocq: `Z.gcd_opp_l`, read through `natAbs` (`Int.gcd` is `Nat.gcd` of the absolute values; core's
-- `Int.natAbs_neg` is axiom-free).
/-- Exact negation of a folded constant; a source magnitude gains its sign from a unary minus. -/
theorem float_constant_neg_canonical : ∀ q : Float.Constant,
    decide (Int.gcd (- Float.numerator q) (Float.denominator q : Int) = 1) = true := by
  intro q
  have H : Int.gcd (- Float.numerator q) (Float.denominator q : Int)
      = Int.gcd (Float.numerator q) (Float.denominator q : Int) := by
    show Nat.gcd (- Float.numerator q).natAbs _ = Nat.gcd (Float.numerator q).natAbs _
    rw [Int.natAbs_neg]
  rw [H]
  exact Float.canonical q
def float_constant_neg (q : Float.Constant) : Float.Constant :=
  Float.MakeConstant (- Float.numerator q) (Float.denominator q) (Float.denominator_pos q)
    (float_constant_neg_canonical q)
def constant_neg (c : Constant) : Option Constant :=
  match c with
  | CInt z     => some (CInt (- z))
  | CFloat q   => some (CFloat (float_constant_neg q))
  | CComplex cc => some (CComplex (Complex.MakeConstant
      (float_constant_neg (Complex.exact_real cc)) (float_constant_neg (Complex.exact_imaginary cc))))
  | CString _ => none
  | CBool _ => none

/-- The exact numeric embedding of a folded constant as a floating component, with no rounding. -/
def constant_to_float (c : Constant) : Option Float.Constant :=
  match c with
  | CInt z   => some (Float.constant_of_Z z)
  | CFloat q => some q
  | CComplex _ => none
  | CString _ => none
  | CBool _ => none
def complex_of_constants (re im : Constant) : Option Constant :=
  match constant_to_float re, constant_to_float im with
  | some r, some i => some (CComplex (Complex.MakeConstant r i))
  | some _, none => none
  | none, some _ => none
  | none, none => none

/-- Defaulting turns an untyped constant into a typed one; an overflowing bare numeric constant has no
    default. -/
def default_constant (c : Constant) : Option ResolvedConstant :=
  match c with
  | CBool b    => some (mk_rc BoolForm (TCBool b))
  | CString s  => some (mk_rc StringForm (TCString s))
  | CInt z     => match bool_true_dec (Integer.representableb Integer.Kind.Int z) with
                  | .inl H => some (mk_rc (IntegerForm Integer.Kind.Int) (TCInt Integer.Kind.Int z H))
                  | .inr _ => none
  | CFloat q   => match Float.round_typed_float F64 q with
                  | some v => some (mk_rc (FloatForm F64) (TCFloat F64 v))
                  | none   => none
  | CComplex cc => match Complex.round_typed C128 cc with
                   | some v => some (mk_rc (ComplexForm C128) (TCComplex C128 v))
                   | none   => none

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A source name's resolved FORM meaning; contextual policy (complex/println/iota/nil) lives in Facts, not
    here. -/
inductive NameMeaning : Type
  | NMConversionForm : TypeForm → NameMeaning
  | NMValueConstant  : Constant → NameMeaning
  | NMNoFormMeaning

open NameMeaning

def predeclared_meaning (n : Names.PredeclaredName) : NameMeaning :=
  match n with
  | .PBool       => NMConversionForm BoolForm
  | .PString     => NMConversionForm StringForm
  | .PInt        => NMConversionForm (IntegerForm Integer.Kind.Int)
  | .PInt8       => NMConversionForm (IntegerForm Integer.Kind.Int8)
  | .PInt16      => NMConversionForm (IntegerForm Integer.Kind.Int16)
  | .PInt32      => NMConversionForm (IntegerForm Integer.Kind.Int32)
  | .PInt64      => NMConversionForm (IntegerForm Integer.Kind.Int64)
  | .PUint       => NMConversionForm (IntegerForm Integer.Kind.Uint)
  | .PUint8      => NMConversionForm (IntegerForm Integer.Kind.Uint8)
  | .PUint16     => NMConversionForm (IntegerForm Integer.Kind.Uint16)
  | .PUint32     => NMConversionForm (IntegerForm Integer.Kind.Uint32)
  | .PUint64     => NMConversionForm (IntegerForm Integer.Kind.Uint64)
  | .PByte       => NMConversionForm (IntegerForm Integer.Kind.Uint8)
  | .PRune       => NMConversionForm (IntegerForm Integer.Kind.Int32)
  | .PFloat32    => NMConversionForm (FloatForm F32)
  | .PFloat64    => NMConversionForm (FloatForm F64)
  | .PComplex64  => NMConversionForm (ComplexForm C64)
  | .PComplex128 => NMConversionForm (ComplexForm C128)
  | .PTrue       => NMValueConstant (CBool true)
  | .PFalse      => NMValueConstant (CBool false)
  | .PAny | .PComparable | .PError | .PUintptr | .PIota | .PNil
  | .PAppend | .PCap | .PClear | .PClose | .PComplex | .PCopy | .PDelete | .PImag | .PLen
  | .PMake | .PMax | .PMin | .PNew | .PPanic | .PPrint | .PPrintln | .PReal | .PRecover => NMNoFormMeaning

end Fido.Compilable.TypeResolution
