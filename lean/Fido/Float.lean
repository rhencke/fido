-- Port of Float.v (lean/README.md).
import Fido.SpecFloat

/-! divergences:
  * `positive` is `Nat` with `0 < n` carried (README).  `Constant` therefore carries the proof as one extra
    `Prop` field, `denominator_pos : 0 < denominator`, and `reduce_constant n d` and the lemmas quantified over
    a positive `d` take the hypothesis `0 < d`; `Zpos d` is the cast `(d : Int)`.  The `.v`'s `positive`
    literals `2%positive` / `(10 ^ 330)%positive` are the `Nat`s `2` / `10 ^ 330`.
  * `Z.to_pos` has no counterpart: where the `.v` applies it to a `Z` known positive, the port takes the `Nat`
    directly — `Z.to_pos (2 ^ (-e))` is `2 ^ (-e).toNat`, `Z.to_pos (10 ^ (-exp))` is `10 ^ (-exp).toNat`, and
    `Z.to_pos (Zpos d / Z.gcd n (Zpos d))` is `((d : Int) / Int.gcd n d).toNat` (`Int.toNat`, which agrees with
    `Z.to_pos` on every positive argument).
  * `Z.gcd` is `Int.gcd`, which returns a `Nat` (it is `Nat.gcd` of the absolute values, as `Z.gcd` is); a
    `Z`-typed use of it is the cast `(Int.gcd n d : Int)`, and every fact stated about it — the `canonical`
    field, the `… = 1` of `constant_canonical` and `reduce_well_formed`, the `0 < …` of `gcd_den_pos` — is
    stated in `Nat` (`Z.gcd` is nonnegative, so `= 1` and `0 <` mean the same in either type).
  * `Z.div` / `Z.modulo` (floor division: the remainder takes the divisor's sign) are Lean's `/` and `%` on
    `Int` (`Int.ediv` / `Int.emod`, Euclidean: the remainder is nonnegative).  The two agree exactly when the
    divisor is positive, and every divisor in this module is: `2 ^ (-e)` in `ieee_to_Z` and
    `ieee_to_constant`, `10 ^ (-exp)` in `decimal_to_constant`, and `Z.gcd n (Zpos d)` (positive by
    `gcd_den_pos`) in `reduce_constant`.  SpecFloat.lean says the same of `Z.div_eucl`.
  * `Z.pow` takes a `Z` exponent and Lean's takes a `Nat`: `2 ^ e` is `2 ^ e.toNat` under `0 ≤ e`, `2 ^ (-e)`
    is `2 ^ (-e).toNat` under `e < 0`, likewise for `10 ^ exp`; `10 ^ 40` is `(10 : Int) ^ 40`.
  * `S754_finite s 0 e` is expressible (SpecFloat.lean's `m : Nat` carries no positivity), so `ieee_to_Z`,
    `ieee_to_constant`, `strip_neg_zero` and `ieee_repr_dec` accept one input Rocq cannot write; no operation
    produces it and no statement here excludes it (a `TypedConstant`'s `rounded` is in the image of
    `round_ieee`, and `binary_round_aux` emits only nonzero mantissas).
  * Axiom closure (the audit's finding; no statement changes): every proof about `Int.gcd` or `Int` division
    on a variable (`gcd_z_1`, `gcd_den_pos`, `reduce_well_formed`, `constant_canonical_unique`, …) carries
    `propext` and `Quot.sound`, and so does everything built on one (`constant_of_Z`, `reduce_constant` and
    their uses); none carries `Classical.choice`.  Core's `Nat.gcd` is well-founded recursion, so each of
    its unfolding equations (`Nat.gcd_zero_left`, `Nat.gcd_succ`, …) goes through `WellFounded.fix_eq` —
    `funext`, hence `Quot.sound` — and core proves its `Nat`/`Int` divisibility, division and multiplication
    lemmas (`Nat.gcd_dvd_left`, `Nat.dvd_antisymm`, `Int.mul_ediv_cancel'`, `Int.mul_comm`, …) with
    `simp`/`omega`, hence `propext`.  Rocq's `Z.gcd` is structural, so Float.v is axiom-free; removing these
    here would take a second, structural gcd, which leaves the README's `Z.gcd ↦ Int.gcd` mapping.  Core's
    `Int.lt_toNat` and `Int.natAbs_ediv` reach `Classical.choice` and are not used (`toNat_pos` and
    `natAbs_ediv_of_dvd` are by hand).
  * `Z.abs c` is `((Int.natAbs c : Nat) : Int)`, `Z.rem` is `Int.tmod` (both truncate toward zero), and the
    boolean stdlib tests (`Z.eqb`, `Z.leb`, `Z.ltb`) are `decide` on the corresponding propositions, so the
    `canonical` field reads `decide (Int.gcd numerator denominator = 1) = true`.
  * `{r | P r} + {Q}` (a `sumor`) is `{r // P r} ⊕' Q` (`PSum`, as in Machine.lean); `option_map` is
    `Option.map`.
  * `UIP_dec Bool.bool_dec` is definitional proof irrelevance (`rfl` after `subst`).  Rocq's `Example`s are
    `theorem`s; the two `Fail Definition` negative checks have no positive counterpart and are not declarations.
  * `reflexivity` and `discriminate` on closed computations are `decide`, and `vm_compute; reflexivity` is
    `decide +kernel` (README: kernel `decide`; the kernel, like Rocq's VM, evaluates `10 ^ 330` where the
    elaborator's literal folding stops at exponent 256).  `Constant` and `TypedConstant` derive `DecidableEq`
    for those equalities (Rocq decides them by conversion), and `round_typed_neg_underflow_f64` first decides
    the typed constant the scrutinee evaluates to, since its `match` statement is not itself `Decidable`.
  * `exact` is a Lean keyword, so the `TypedConstant` field of that name is written `«exact»` at every use.
  * Catch-all `_` match arms are enumerated (Integer.lean: a wildcard arm compiles through a
    `propext`-dependent helper in Lean 4.33).
-/

namespace Fido.Float
open Fido.SpecFloat (spec_float S754_zero S754_infinity S754_nan S754_finite SFdiv)

inductive Kind : Type
  | F32 | F64
  deriving DecidableEq, Repr

open Kind

def kind_equalb (a b : Kind) : Bool :=
  match a, b with
  | F32, F32 => true
  | F64, F64 => true
  | F32, F64 => false
  | F64, F32 => false

theorem kind_equalb_spec : ∀ a b, kind_equalb a b = true ↔ a = b := by
  intro a b; cases a <;> cases b <;> decide

/-- binary32 is (prec 24, emax 128) and binary64 is (prec 53, emax 1024), the two pairs SpecFloat takes. -/
def precision (ft : Kind) : Int := match ft with | F32 => 24 | F64 => 53
def maximum_exponent (ft : Kind) : Int := match ft with | F32 => 128 | F64 => 1024

theorem precision_f32 : precision F32 = 24 := rfl
theorem precision_f64 : precision F64 = 53 := rfl
theorem maximum_exponent_f32 : maximum_exponent F32 = 128 := rfl
theorem maximum_exponent_f64 : maximum_exponent F64 = 1024 := rfl

-- Rocq's `Record` generates no injectivity or size lemmas; the auto-generated ones would be the module's only
-- `propext` users.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An exact rational in lowest terms by construction, so a non-reduced fraction such as 2/4 has no value. -/
structure Constant : Type where
  MakeConstant ::
  numerator : Int
  denominator : Nat
  denominator_pos : 0 < denominator
  canonical : decide (Int.gcd numerator denominator = 1) = true
  deriving DecidableEq

export Constant (MakeConstant numerator denominator denominator_pos canonical)

theorem gcd_z_1 : ∀ z : Int, decide (Int.gcd z 1 = 1) = true :=
  fun z => decide_eq_true (Nat.gcd_one_right z.natAbs)

def constant_of_Z (z : Int) : Constant := MakeConstant z 1 Nat.zero_lt_one (gcd_z_1 z)

def constant_zero : Constant := constant_of_Z 0

/-- An exact integer embedded as a mantissa fed only to `SFdiv`, which normalizes it. -/
def ieee_of_Z (z : Int) : spec_float :=
  match z with
  | .ofNat 0 => S754_zero false
  | .ofNat (p + 1) => S754_finite false (p + 1) 0
  | .negSucc p => S754_finite true (p + 1) 0

def round_ieee (ft : Kind) (a : Constant) : spec_float :=
  SFdiv (precision ft) (maximum_exponent ft) (ieee_of_Z (numerator a)) (ieee_of_Z (denominator a))

def cond_Zopp (s : Bool) (m : Int) : Int := if s then -m else m

def ieee_to_Z (v : spec_float) : Option Int :=
  match v with
  | S754_zero _ => some 0
  | S754_finite s m e =>
      let n := cond_Zopp s m
      if 0 ≤ e then some (n * 2 ^ e.toNat)                 -- integer by construction
      else let d : Int := 2 ^ (-e).toNat                     -- dyadic n*2^e; integer iff 2^(-e) | n
           if n % d = 0 then some (n / d) else none
  | S754_infinity _ => none
  | S754_nan => none

/-- A double-rounding witness: direct binary32 rounds up where binary64-then-binary32 rounds to even, down. -/
def single_rounding_x : Constant := constant_of_Z 2305843146652647425

theorem single_rounding_direct_f32 :
    ieee_to_Z (round_ieee F32 single_rounding_x) = some 2305843284091600896 := by decide

theorem single_rounding_double_f32_via_f64 :
    ieee_to_Z (SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1)) = some 2305843009213693952 := by
  decide

theorem single_rounding_direct_differs_double :
    round_ieee F32 single_rounding_x ≠ SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1) := by
  decide

theorem round_f32_2p24_plus1 :
    ieee_to_Z (round_ieee F32 (constant_of_Z 16777217)) = some 16777216 := by decide

theorem round_f64_2p53_plus1 :
    ieee_to_Z (round_ieee F64 (constant_of_Z 9007199254740993)) = some 9007199254740992 := by decide

theorem round_f32_exact_small : ieee_to_Z (round_ieee F32 (constant_of_Z 3)) = some 3 := by decide
theorem round_f64_exact_small : ieee_to_Z (round_ieee F64 (constant_of_Z 42)) = some 42 := by decide


def constant_canonical (a : Constant) : Prop :=
  Int.gcd (numerator a) (denominator a) = 1

def constant_eq (a b : Constant) : Prop :=
  numerator a * denominator b = numerator b * denominator a

def constant_equalb (a b : Constant) : Bool :=
  decide (numerator a * denominator b = numerator b * denominator a)

theorem constant_equalb_spec : ∀ a b, constant_equalb a b = true ↔ constant_eq a b := by
  intro a b; unfold constant_equalb constant_eq; exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem constant_of_Z_canonical : ∀ z, constant_canonical (constant_of_Z z) :=
  fun z => Nat.gcd_one_right z.natAbs

theorem constant_zero_canonical : constant_canonical constant_zero := constant_of_Z_canonical 0

theorem constant_canonical_intrinsic : ∀ a, constant_canonical a := by
  intro a; unfold constant_canonical; exact of_decide_eq_true (canonical a)

theorem numerator_denominator_eq : ∀ a b, numerator a = numerator b → denominator a = denominator b → a = b := by
  intro a b Hn Hd
  cases a with | MakeConstant na da pa wa =>
  cases b with | MakeConstant nb db pb wb =>
  have Hn' : na = nb := Hn
  have Hd' : da = db := Hd
  subst Hn'; subst Hd'
  rfl

theorem gcd_den_pos : ∀ (n : Int) (d : Nat), 0 < d → 0 < Int.gcd n d := by
  intro n d Hd
  show 0 < Nat.gcd n.natAbs d
  exact Nat.gcd_pos_of_pos_right _ Hd

theorem reduce_den_pos : ∀ (n : Int) (d : Nat), 0 < d → 0 < (d : Int) / (Int.gcd n d : Int) := by
  intro n d Hd
  exact Int.ediv_pos_of_pos_of_dvd (by omega) (by omega) (Int.gcd_dvd_right n d)

theorem reduce_zpos : ∀ (n : Int) (d : Nat), 0 < d →
    ((((d : Int) / (Int.gcd n d : Int)).toNat : Nat) : Int) = (d : Int) / (Int.gcd n d : Int) :=
  fun n d Hd => Int.toNat_of_nonneg (Int.le_of_lt (reduce_den_pos n d Hd))

/-- `(a / g).natAbs = a.natAbs / g` when `g ∣ a`: the Rocq proof's `Zdivide_Zdiv_eq` read through `natAbs`. -/
private theorem natAbs_ediv_of_dvd (a : Int) (g : Nat) (Hg : 0 < g) (H : (g : Int) ∣ a) :
    (a / (g : Int)).natAbs = a.natAbs / g := by
  obtain ⟨k, Hk⟩ := H
  rw [Hk, Int.mul_ediv_cancel_left k (by omega), Int.natAbs_mul, Int.natAbs_natCast,
    Nat.mul_div_cancel_left _ Hg]

theorem reduce_well_formed : ∀ (n : Int) (d : Nat), 0 < d →
    decide (Int.gcd (n / (Int.gcd n d : Int)) ((((d : Int) / (Int.gcd n d : Int)).toNat : Nat)) = 1) = true := by
  intro n d Hd
  apply decide_eq_true
  rw [reduce_zpos n d Hd]
  have Hg : 0 < Int.gcd n d := gcd_den_pos n d Hd
  show Nat.gcd (n / (Int.gcd n d : Int)).natAbs (((d : Int) / (Int.gcd n d : Int)).natAbs) = 1
  rw [natAbs_ediv_of_dvd _ _ Hg (Int.gcd_dvd_left n d), natAbs_ediv_of_dvd _ _ Hg (Int.gcd_dvd_right n d),
    Int.natAbs_natCast]
  show Nat.gcd (n.natAbs / Nat.gcd n.natAbs d) (d / Nat.gcd n.natAbs d) = 1
  rw [Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)]
  exact Nat.div_self Hg

-- Rocq: `Z2Pos.id`.  By the `Int` constructors, so that nothing classical enters `reduce_constant`'s proof
-- fields (core's `Int.lt_toNat` would).
private theorem toNat_pos : ∀ x : Int, 0 < x → 0 < x.toNat
  | .ofNat (n + 1), _ => Nat.succ_pos n
  | .ofNat 0, h => nomatch h
  | .negSucc _, h => nomatch h

def reduce_constant (n : Int) (d : Nat) (Hd : 0 < d) : Constant :=
  MakeConstant (n / (Int.gcd n d : Int)) (((d : Int) / (Int.gcd n d : Int)).toNat)
    (toNat_pos _ (reduce_den_pos n d Hd)) (reduce_well_formed n d Hd)

theorem reduce_constant_canonical : ∀ n d (Hd : 0 < d), constant_canonical (reduce_constant n d Hd) :=
  fun _ _ _ => constant_canonical_intrinsic _

theorem reduce_constant_eq : ∀ n d (Hd : 0 < d),
    numerator (reduce_constant n d Hd) * d = n * denominator (reduce_constant n d Hd) := by
  intro n d Hd
  show n / (Int.gcd n d : Int) * d = n * ((((d : Int) / (Int.gcd n d : Int)).toNat : Nat) : Int)
  rw [reduce_zpos n d Hd]
  have Hn : (Int.gcd n d : Int) * (n / (Int.gcd n d : Int)) = n := Int.mul_ediv_cancel' (Int.gcd_dvd_left n d)
  have Hdd : (Int.gcd n d : Int) * ((d : Int) / (Int.gcd n d : Int)) = d :=
    Int.mul_ediv_cancel' (Int.gcd_dvd_right n d)
  calc n / (Int.gcd n d : Int) * d
      = n / (Int.gcd n d : Int) * ((Int.gcd n d : Int) * ((d : Int) / (Int.gcd n d : Int))) :=
        congrArg (n / (Int.gcd n d : Int) * ·) Hdd.symm
    _ = (Int.gcd n d : Int) * (n / (Int.gcd n d : Int)) * ((d : Int) / (Int.gcd n d : Int)) := by
        rw [Int.mul_left_comm, Int.mul_assoc]
    _ = n * ((d : Int) / (Int.gcd n d : Int)) := congrArg (· * ((d : Int) / (Int.gcd n d : Int))) Hn

/-- Every constant is in lowest terms, so rational equality is Leibniz equality. -/
theorem constant_canonical_unique : ∀ a b, constant_eq a b → a = b := by
  intro a b Heq
  have Ha : Nat.gcd (numerator a).natAbs (denominator a) = 1 := constant_canonical_intrinsic a
  have Hb : Nat.gcd (numerator b).natAbs (denominator b) = 1 := constant_canonical_intrinsic b
  -- `constant_canonical` IS coprimality; a coprime divisor of a product divides the other factor (Gauss).
  have HeqN : (numerator a).natAbs * denominator b = (numerator b).natAbs * denominator a := by
    have H := congrArg Int.natAbs Heq
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at H
    exact H
  have Hda_dvd : denominator a ∣ denominator b :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.gcd_comm _ _).trans Ha)
      ⟨(numerator b).natAbs, by rw [HeqN, Nat.mul_comm]⟩
  have Hdb_dvd : denominator b ∣ denominator a :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.gcd_comm _ _).trans Hb)
      ⟨(numerator a).natAbs, by rw [← HeqN, Nat.mul_comm]⟩
  have Hdeq : denominator a = denominator b := Nat.dvd_antisymm Hda_dvd Hdb_dvd
  have Hneq : numerator a = numerator b := by
    unfold constant_eq at Heq
    rw [Hdeq] at Heq
    exact Int.eq_of_mul_eq_mul_right (by have := denominator_pos b; omega) Heq
  exact numerator_denominator_eq a b Hneq Hdeq

theorem constant_equalb_eq : ∀ a b, constant_equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H; exact constant_canonical_unique a b ((constant_equalb_spec a b).1 H)
  · intro H; subst H; exact decide_eq_true rfl

/-- A rounded `spec_float` back to an exact constant; an infinity or a NaN has no exact constant. -/
def ieee_to_constant (v : spec_float) : Option Constant :=
  match v with
  | S754_zero _ => some constant_zero
  | S754_finite s m e =>
      let n := cond_Zopp s m
      if 0 ≤ e then some (constant_of_Z (n * 2 ^ e.toNat))
      else some (reduce_constant n (2 ^ (-e).toNat) (Nat.two_pow_pos _))
  | S754_infinity _ => none
  | S754_nan => none

def decimal_max_coeff : Int := 10 ^ 40   -- |coeff| < 10^40  (<= 40 significant digits)
def decimal_max_exp   : Int := 4096

/-- Canonical: zero is exactly (0,0), and a nonzero coefficient has no removable factor of ten. -/
def decimal_canonicalb (c e : Int) : Bool :=
  if c = 0 then decide (e = 0) else !(decide (Int.tmod c 10 = 0))

def decimal_wfb (c e : Int) : Bool :=
  decimal_canonicalb c e
  && decide (((Int.natAbs c : Nat) : Int) < decimal_max_coeff)
  && decide (-decimal_max_exp ≤ e) && decide (e ≤ decimal_max_exp)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Decimal : Type where
  MakeDecimal ::
  coefficient : Int
  exponent : Int
  canonical_decimal : decimal_wfb coefficient exponent = true

export Decimal (MakeDecimal coefficient exponent canonical_decimal)

def decimal_equalb (a b : Decimal) : Bool :=
  decide (coefficient a = coefficient b) && decide (exponent a = exponent b)

-- Rocq: `Bool.andb_true_iff`, one direction, by cases (no `propext`).
private theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, true, h => nomatch h
  | false, false, h => nomatch h

theorem decimal_equalb_spec : ∀ a b, decimal_equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H
    obtain ⟨H1, H2⟩ := band_true H
    cases a with | MakeDecimal ca ea pa =>
    cases b with | MakeDecimal cb eb pb =>
    have h1 : ca = cb := of_decide_eq_true H1
    have h2 : ea = eb := of_decide_eq_true H2
    subst h1; subst h2
    rfl
  · intro H
    subst H
    show (decide (coefficient a = coefficient a) && decide (exponent a = exponent a)) = true
    rw [decide_eq_true (Eq.refl (coefficient a)), decide_eq_true (Eq.refl (exponent a))]
    rfl

/-- The exact rational value of the literal, with no rounding: raw interpretation is exact. -/
def decimal_to_constant (coeff exp : Int) : Constant :=
  if 0 ≤ exp then constant_of_Z (coeff * 10 ^ exp.toNat)
  else reduce_constant coeff (10 ^ (-exp).toNat) (Nat.pow_pos (by decide))

def decimal_value (d : Decimal) : Constant :=
  decimal_to_constant (coefficient d) (exponent d)

theorem decimal_value_canonical : ∀ d, constant_canonical (decimal_value d) :=
  fun _ => constant_canonical_intrinsic _

/-- The one zero literal; its value is unsigned, so there is no negative-zero decimal literal. -/
def decimal_zero : Decimal := MakeDecimal 0 0 rfl

theorem decimal_value_zero : decimal_value decimal_zero = constant_zero := rfl

theorem decimal_zero_unique : ∀ d, coefficient d = 0 → d = decimal_zero := by
  intro d Hc
  cases d with | MakeDecimal c e w =>
  have Hc' : c = 0 := Hc
  subst Hc'
  have Hcan : decide (e = 0) = true := (band_true (band_true (band_true w).1).1).1
  have He : e = 0 := of_decide_eq_true Hcan
  subst He
  rfl

theorem decimal_wfb_max_ok :
    decimal_wfb (decimal_max_coeff - 1) decimal_max_exp = true := by decide
theorem decimal_wfb_coeff_over :
    decimal_wfb decimal_max_coeff 0 = false := by decide
theorem decimal_wfb_exp_over :
    decimal_wfb 1 (decimal_max_exp + 1) = false := by decide
theorem decimal_wfb_trailing_zero_noncanon :
    decimal_wfb 250 0 = false := by decide               -- 250 has a removable factor of ten -> not canonical
theorem decimal_value_1p5 :                                        -- 15 * 10^-1 = 3/2
    numerator (decimal_value (MakeDecimal 15 (-1) rfl)) = 3
    ∧ denominator (decimal_value (MakeDecimal 15 (-1) rfl)) = 2 := by decide
theorem decimal_value_1e6 :
    decimal_value (MakeDecimal 1 6 rfl) = constant_of_Z 1000000 := by decide
theorem decimal_value_neg :                                       -- -15 * 10^-1 = -3/2
    numerator (decimal_value (MakeDecimal (-15) (-1) rfl)) = -3
    ∧ denominator (decimal_value (MakeDecimal (-15) (-1) rfl)) = 2 := by decide
theorem decimal_value_tenth :                                     -- 1 * 10^-1 = 1/10 (the example)
    numerator (decimal_value (MakeDecimal 1 (-1) rfl)) = 1
    ∧ denominator (decimal_value (MakeDecimal 1 (-1) rfl)) = 10 := by decide

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A source float magnitude: a canonical `Decimal` with nonnegative coefficient; a source minus is a `Unary`. -/
structure NonNegativeDecimal : Type where
  MakeNonNegDecimal ::
  nnd_decimal : Decimal
  nnd_nonnegb : decide (0 ≤ coefficient nnd_decimal) = true

export NonNegativeDecimal (MakeNonNegDecimal nnd_decimal nnd_nonnegb)

def nnd_value (d : NonNegativeDecimal) : Constant := decimal_value (nnd_decimal d)
theorem nnd_nonneg (d : NonNegativeDecimal) : 0 ≤ coefficient (nnd_decimal d) :=
  of_decide_eq_true (nnd_nonnegb d)

def nnd_equalb (a b : NonNegativeDecimal) : Bool := decimal_equalb (nnd_decimal a) (nnd_decimal b)
theorem nnd_equalb_spec : ∀ a b, nnd_equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H
    have H' := (decimal_equalb_spec _ _).1 H
    cases a with | MakeNonNegDecimal da pa =>
    cases b with | MakeNonNegDecimal db pb =>
    have h : da = db := H'
    subst h
    rfl
  · intro H; subst H; exact (decimal_equalb_spec _ _).2 rfl

def nnd_zero : NonNegativeDecimal := MakeNonNegDecimal decimal_zero rfl

/-- Zero-sign normalization: a constant has no signed zero, so a zero result normalizes to positive zero. -/
def strip_neg_zero (v : spec_float) : spec_float :=
  match v with
  | S754_zero _ => S754_zero false
  | S754_infinity s => S754_infinity s
  | S754_nan => S754_nan
  | S754_finite s m e => S754_finite s m e

/-- A `sumor` decides the read-back once and carries its proof, so nothing downstream re-abstracts a motive. -/
def ieee_repr_dec (v : spec_float) :
    {r : Constant // ieee_to_constant v = some r} ⊕' (ieee_to_constant v = none) :=
  (fun (o : Option Constant) (H : ieee_to_constant v = o) =>
    match o, H with
    | some r, H => .inl ⟨r, H⟩
    | none, H => .inr H) (ieee_to_constant v) rfl

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A float typed constant is a purely static carrier of one rounding's exact rational and rounded
    representation. -/
structure TypedConstant (ft : Kind) : Type where
  MakeTypedConstant ::
  «exact»  : Constant
  rounded  : spec_float
  formed   : ∃ q : Constant, rounded = strip_neg_zero (round_ieee ft q)
  coherent : ieee_to_constant rounded = some «exact»
  deriving DecidableEq

export TypedConstant (MakeTypedConstant «exact» rounded formed coherent)

/-- The sole rounding-from-exact typed-float formation authority: round once at `ft`, normalize zero, derive
    both. -/
def round_typed_float (ft : Kind) (q : Constant) : Option (TypedConstant ft) :=
  let r0 := strip_neg_zero (round_ieee ft q)
  match ieee_repr_dec r0 with
  | .inl ⟨r, Hr⟩ => some (MakeTypedConstant r r0 ⟨q, rfl⟩ Hr)
  | .inr _       => none

/-- A successful rounding retains exactly the destination-format rounded value as its representation. -/
theorem round_typed_float_rounded : ∀ ft q tc,
    round_typed_float ft q = some tc → rounded tc = strip_neg_zero (round_ieee ft q) := by
  intro ft q tc
  unfold round_typed_float
  dsimp only
  cases ieee_repr_dec (strip_neg_zero (round_ieee ft q)) with
  | inl x =>
    cases x with | mk r Hr =>
    intro H
    cases H
    rfl
  | inr Hn => intro H; cases H

/-- The exact-rational rounding is the `exact` projection of the typed result, not a second rounding call. -/
def round_constant (ft : Kind) (a : Constant) : Option Constant :=
  Option.map «exact» (round_typed_float ft a)

theorem round_constant_typed : ∀ ft q,
    round_constant ft q = Option.map «exact» (round_typed_float ft q) := fun _ _ => rfl

def Representable (ft : Kind) (a : Constant) : Prop :=
  ∃ r, round_constant ft a = some r

def representableb (ft : Kind) (a : Constant) : Bool :=
  match round_constant ft a with | some _ => true | none => false

theorem representableb_spec :
    ∀ ft a, representableb ft a = true ↔ Representable ft a := by
  intro ft a
  unfold representableb Representable
  cases E : round_constant ft a with
  | some r => exact ⟨fun _ => ⟨r, rfl⟩, fun _ => rfl⟩
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

theorem round_typed_float_representable : ∀ ft q,
    representableb ft q = true ↔ ∃ tc, round_typed_float ft q = some tc := by
  intro ft q
  unfold representableb round_constant
  cases E : round_typed_float ft q with
  | some tc => exact ⟨fun _ => ⟨tc, rfl⟩, fun _ => rfl⟩
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

/-- The rounded representation is in the image of `round_ieee ft`, so the format index `ft` is load-bearing. -/
theorem typed_format_image : ∀ ft (tc : TypedConstant ft),
    ∃ q, rounded tc = strip_neg_zero (round_ieee ft q) := fun _ tc => formed tc

/-- Read-back coherence: reading the retained representation yields the retained exact rational. -/
theorem typed_readback : ∀ ft (tc : TypedConstant ft),
    ieee_to_constant (rounded tc) = some («exact» tc) := fun _ tc => coherent tc

/-- Positive-zero-or-finite shape: negative zero, infinity and NaN are unconstructible as typed constants. -/
theorem typed_not_neg_zero : ∀ ft (tc : TypedConstant ft), rounded tc ≠ S754_zero true := by
  intro ft tc H
  obtain ⟨q, Hq⟩ := formed tc
  rw [H] at Hq
  revert Hq
  cases round_ieee ft q <;> intro Hq <;> cases Hq
theorem typed_not_nan : ∀ ft (tc : TypedConstant ft), rounded tc ≠ S754_nan := by
  intro ft tc H
  have Hc := coherent tc
  rw [H] at Hc
  cases Hc
theorem typed_not_inf : ∀ ft (tc : TypedConstant ft) s, rounded tc ≠ S754_infinity s := by
  intro ft tc s H
  have Hc := coherent tc
  rw [H] at Hc
  cases Hc

theorem round_const_single_rounding_direct_f32 :
    round_constant F32 single_rounding_x = some (constant_of_Z 2305843284091600896) := by decide +kernel
theorem round_const_single_rounding_double_f32 :
    ieee_to_constant (SFdiv 24 128 (round_ieee F64 single_rounding_x) (ieee_of_Z 1))
      = some (constant_of_Z 2305843009213693952) := by decide
theorem round_const_overflow_f32 :
    round_constant F32 (constant_of_Z (10 ^ 40)) = none := by decide +kernel
theorem round_const_underflow_f64 :
    round_constant F64 (reduce_constant 1 (10 ^ 330) (Nat.pow_pos (by decide))) = some constant_zero := by
  decide +kernel
theorem round_const_source_zero_f64 :
    round_constant F64 constant_zero = some constant_zero := by decide +kernel   -- the canonical zero rounds to +0
theorem representableb_single_rounding_f32 : representableb F32 single_rounding_x = true := by decide +kernel
theorem representableb_overflow_f32 : representableb F32 (constant_of_Z (10 ^ 40)) = false := by decide +kernel

/-- The honest carrier is constructible, and a negative-zero or NaN representation is refused by the fields. -/
theorem tfc_five_f64_ok :
    match round_typed_float F64 (constant_of_Z 5) with | some _ => True | none => False := by
  exact True.intro

theorem round_typed_neg_underflow_f64 :
    match round_typed_float F64 (reduce_constant (-1) (10 ^ 330) (Nat.pow_pos (by decide))) with
    | some tc => «exact» tc = constant_zero ∧ rounded tc = S754_zero false
    | none => False := by
  -- Rocq: `vm_compute` evaluates the scrutinee; here the kernel decides it, then the arm is `split; reflexivity`.
  have H : round_typed_float F64 (reduce_constant (-1) (10 ^ 330) (Nat.pow_pos (by decide)))
      = some (MakeTypedConstant constant_zero (S754_zero false)
          ⟨reduce_constant (-1) (10 ^ 330) (Nat.pow_pos (by decide)), by decide +kernel⟩ rfl) := by
    decide +kernel
  rw [H]
  exact And.intro rfl rfl

end Fido.Float
