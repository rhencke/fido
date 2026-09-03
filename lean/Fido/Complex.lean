-- Port of Complex.v (lean/README.md).
import Fido.Float

/-! divergences:
  * Axiom closure (the audit's finding; no statement changes): `propext` and `Quot.sound` enter through
    three Float.lean constants — `Float.constant_zero` (its `canonical` proof `gcd_z_1` goes through core's
    `Nat.gcd_one_right`; core's `Nat.gcd` is well-founded recursion where Rocq's `Z.gcd` is structural),
    `Float.TypedConstant` (its `formed`/`coherent` fields mention `ieee_to_constant`, hence
    `reduce_constant`) and `Float.constant_equalb_eq` — so every constant here that mentions one of them
    inherits both: `zero`, `of_real` and their two lemmas, `constant_imaginary_is_zero`,
    `real_if_imaginary_zero(_some)`, `constant_equalb_spec`, and everything from `TypedConstant` on.
    `Kind`, `kind_equalb(_spec)`, `component_kind`, `component_c64/c128`, `Constant` and `constant_equalb`
    are axiom-free.  Nothing here reaches `Classical.choice`.
  * `exact` is a Lean keyword, so `Float.exact` is written `Float.«exact»` at every use.
  * Catch-all `_` match arms are enumerated (Integer.lean): `kind_equalb`'s two off-diagonal pairs and
    `round_typed`'s three `None` arms.  Lean's match splits on the first discriminant first, so the two
    `_none` lemmas close by a case split on the other component where Rocq's `reflexivity` sufficed.
  * `Arguments MakeTypedConstant {ct} _ _` (and the two projections) is Lean's default — a structure's
    parameter is implicit in its constructor and projections — so it is not written.
-/

namespace Fido.Complex
open Float.Kind (F32 F64)

inductive Kind : Type
  | C64 | C128
  deriving DecidableEq, Repr

open Kind

def kind_equalb (a b : Kind) : Bool :=
  match a, b with
  | C64, C64 => true
  | C128, C128 => true
  | C64, C128 => false
  | C128, C64 => false

theorem kind_equalb_spec : ∀ a b, kind_equalb a b = true ↔ a = b := by
  intro a b; cases a <;> cases b <;> decide

/-- The one component-format mapping; every complex precision and rounding property derives from it. -/
def component_kind (ct : Kind) : Float.Kind :=
  match ct with | C64 => F32 | C128 => F64

theorem component_c64 : component_kind C64 = F32 := rfl
theorem component_c128 : component_kind C128 = F64 := rfl

-- Rocq's `Record` generates no injectivity or size lemmas; the auto-generated ones would be `propext` users.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact complex constant: two canonical rational components, whose canonicality already lives in each. -/
structure Constant : Type where
  MakeConstant ::
  exact_real : Float.Constant
  exact_imaginary : Float.Constant

export Constant (MakeConstant exact_real exact_imaginary)

/-- Componentwise decidable equality; the components are canonical, so this is Leibniz equality. -/
def constant_equalb (a b : Constant) : Bool :=
  Float.constant_equalb (exact_real a) (exact_real b)
  && Float.constant_equalb (exact_imaginary a) (exact_imaginary b)

-- Rocq: `Bool.andb_true_iff`, one direction, by cases (no `propext`).
private theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, true, h => nomatch h
  | false, false, h => nomatch h

theorem constant_equalb_spec : ∀ a b, constant_equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H
    obtain ⟨Hr, Hi⟩ := band_true H
    have Hr' := (Float.constant_equalb_eq _ _).1 Hr
    have Hi' := (Float.constant_equalb_eq _ _).1 Hi
    cases a with | MakeConstant ar ai =>
    cases b with | MakeConstant br bi =>
    have h1 : ar = br := Hr'
    have h2 : ai = bi := Hi'
    subst h1; subst h2
    rfl
  · intro H
    subst H
    have Hr : Float.constant_equalb (exact_real a) (exact_real a) = true :=
      (Float.constant_equalb_eq _ _).2 rfl
    have Hi : Float.constant_equalb (exact_imaginary a) (exact_imaginary a) = true :=
      (Float.constant_equalb_eq _ _).2 rfl
    show (Float.constant_equalb (exact_real a) (exact_real a)
          && Float.constant_equalb (exact_imaginary a) (exact_imaginary a)) = true
    rw [Hr, Hi]
    rfl

def zero : Constant := MakeConstant Float.constant_zero Float.constant_zero
def of_real (q : Float.Constant) : Constant := MakeConstant q Float.constant_zero

theorem constant_real_of_real : ∀ q, exact_real (of_real q) = q := fun _ => rfl
theorem constant_imaginary_of_real : ∀ q, exact_imaginary (of_real q) = Float.constant_zero := fun _ => rfl

def constant_imaginary_is_zero (c : Constant) : Bool :=
  Float.constant_equalb (exact_imaginary c) Float.constant_zero

/-- Project the exact real component only when the imaginary component is exactly zero; this never rounds. -/
def real_if_imaginary_zero (c : Constant) : Option Float.Constant :=
  if constant_imaginary_is_zero c then some (exact_real c) else none

theorem real_if_imaginary_zero_some : ∀ c q,
    real_if_imaginary_zero c = some q → constant_imaginary_is_zero c = true ∧ exact_real c = q := by
  intro c q
  unfold real_if_imaginary_zero
  cases constant_imaginary_is_zero c with
  | true => intro H; exact ⟨rfl, Option.some.inj H⟩
  | false => intro H; cases H

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The typed complex constant: two already-coherent typed components, so no coherence field is duplicated. -/
structure TypedConstant (ct : Kind) : Type where
  MakeTypedConstant ::
  typed_real : Float.TypedConstant (component_kind ct)
  typed_imaginary : Float.TypedConstant (component_kind ct)

export TypedConstant (MakeTypedConstant typed_real typed_imaginary)

/-- Both projections are pure component reads: no rounding, no reconstruction. -/
def typed_exact {ct : Kind} (tc : TypedConstant ct) : Constant :=
  MakeConstant (Float.«exact» (typed_real tc)) (Float.«exact» (typed_imaginary tc))

theorem typed_exact_real : ∀ ct (tc : TypedConstant ct),
    exact_real (typed_exact tc) = Float.«exact» (typed_real tc) := fun _ _ => rfl
theorem typed_exact_imaginary : ∀ ct (tc : TypedConstant ct),
    exact_imaginary (typed_exact tc) = Float.«exact» (typed_imaginary tc) := fun _ _ => rfl

/-- The sole rounding-from-exact formation authority: round each component once at its destination format, or
    fail. -/
def round_typed (ct : Kind) (c : Constant) : Option (TypedConstant ct) :=
  match Float.round_typed_float (component_kind ct) (exact_real c),
        Float.round_typed_float (component_kind ct) (exact_imaginary c) with
  | some tr, some ti => some (MakeTypedConstant tr ti)
  | some _, none => none
  | none, some _ => none
  | none, none => none

theorem round_typed_components : ∀ ct c tc,
    round_typed ct c = some tc →
    Float.round_typed_float (component_kind ct) (exact_real c) = some (typed_real tc)
    ∧ Float.round_typed_float (component_kind ct) (exact_imaginary c) = some (typed_imaginary tc) := by
  intro ct c tc
  unfold round_typed
  cases Float.round_typed_float (component_kind ct) (exact_real c) with
  | some tr =>
    cases Float.round_typed_float (component_kind ct) (exact_imaginary c) with
    | some ti =>
      intro H
      have H' : MakeTypedConstant tr ti = tc := Option.some.inj H
      subst H'
      exact ⟨rfl, rfl⟩
    | none => intro H; cases H
  | none =>
    cases Float.round_typed_float (component_kind ct) (exact_imaginary c) with
    | some ti => intro H; cases H
    | none => intro H; cases H

theorem round_typed_real_none : ∀ ct c,
    Float.round_typed_float (component_kind ct) (exact_real c) = none → round_typed ct c = none := by
  intro ct c H
  unfold round_typed
  rw [H]
  cases Float.round_typed_float (component_kind ct) (exact_imaginary c) <;> rfl

theorem round_typed_imaginary_none : ∀ ct c,
    Float.round_typed_float (component_kind ct) (exact_imaginary c) = none → round_typed ct c = none := by
  intro ct c H
  unfold round_typed
  rw [H]
  cases Float.round_typed_float (component_kind ct) (exact_real c) <;> rfl

def Representable (ct : Kind) (c : Constant) : Prop :=
  ∃ tc, round_typed ct c = some tc

def representableb (ct : Kind) (c : Constant) : Bool :=
  match round_typed ct c with | some _ => true | none => false

theorem representableb_spec : ∀ ct c,
    representableb ct c = true ↔ Representable ct c := by
  intro ct c
  unfold representableb Representable
  cases E : round_typed ct c with
  | some tc => exact ⟨fun _ => ⟨tc, rfl⟩, fun _ => rfl⟩
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

end Fido.Complex
