-- Port of Decimal.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  - `positive` is `Nat` under `0 < n` (README): `positive_digits` recurses on `n / 2` by well-founded
    recursion, reading the carry bit as `n % 2` (Rocq's `xO`/`xI` arms are the two values of that bit);
    `positive_digits B 0 = []` has no Rocq counterpart, and each lemma quantified over a positive carries
    `0 < n`.  Being well-founded, the definition does not unfold under `rfl`/`decide`; `rw`, `simp` and
    `decide +kernel` all evaluate it.
  - Rocq's `Forall P ds` is `∀ d ∈ ds, P d`: core Lean 4.33 has no `List.Forall` (a Mathlib definition).
    The two are equivalent by Rocq's `Forall_forall`, which is how Render.v consumes these lemmas.
  - `Z` is `Int` (`ofNat n | negSucc n`), so `integer` cases on `.ofNat 0` / `.ofNat (n + 1)` /
    `.negSucc n` in place of `Z0` / `Zpos p` / `Zneg p`; the positive `p` is `n + 1`. -/

namespace Fido.Decimal

def digit (n : Nat) : UInt8 := UInt8.ofNat (48 + n)

def double (B : Nat) : List Nat → Nat → List Nat
  | [], carry => match carry with | 0 => [] | c + 1 => [c + 1]
  | d :: tl, carry => (2 * d + carry) % B :: double B tl ((2 * d + carry) / B)

/-- LSB-first base-`B` digits, recursing on `n / 2` (the positive's own bits), so this is total with no
    step budget. -/
def positive_digits (B : Nat) : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | n + 2 => double B (positive_digits B ((n + 2) / 2)) ((n + 2) % 2)
termination_by n => n
decreasing_by omega

def value (B : Nat) : List Nat → Int
  | [] => 0
  | d :: tl => (d : Int) + (B : Int) * value B tl

theorem double_val : ∀ B ds carry, B ≠ 0 →
    value B (double B ds carry) = 2 * value B ds + (carry : Int) := by
  intro B ds
  induction ds with
  | nil =>
    intro carry _
    cases carry with
    | zero => simp [double, value]
    | succ c => simp [double, value]
  | cons d tl IH =>
    intro carry HB
    simp only [double, value]
    rw [IH _ HB]
    have hz : ((B : Int) * (((2 * d + carry) / B : Nat) : Int) + (((2 * d + carry) % B : Nat) : Int))
        = 2 * (d : Int) + (carry : Int) := by
      have h := congrArg (fun k : Nat => (k : Int)) (Nat.div_add_mod (2 * d + carry) B)
      simp only [Int.natCast_add, Int.natCast_mul] at h
      omega
    rw [Int.mul_add, Int.mul_left_comm]
    omega

theorem positive_digits_val : ∀ B n, B ≠ 0 → 0 < n → value B (positive_digits B n) = (n : Int) := by
  intro B n HB
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro Hn
    match n, IH, Hn with
    | 0, _, Hn => omega
    | 1, _, _ => simp [positive_digits, value]
    | m + 2, IH, _ =>
      rw [positive_digits, double_val _ _ _ HB, IH ((m + 2) / 2) (by omega) (by omega)]
      omega

theorem double_bound : ∀ B ds carry, 2 ≤ B → carry ≤ 1 →
    (∀ d ∈ ds, d < B) → ∀ d ∈ double B ds carry, d < B := by
  intro B ds
  induction ds with
  | nil =>
    intro carry HB Hc _
    cases carry with
    | zero => simp [double]
    | succ c => simp [double]; omega
  | cons d tl IH =>
    intro carry HB Hc Hall
    rw [List.forall_mem_cons] at Hall
    simp only [double, List.forall_mem_cons]
    refine ⟨Nat.mod_lt _ (by omega), IH _ HB ?_ Hall.2⟩
    have : (2 * d + carry) / B < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

theorem positive_digits_bound : ∀ B n, 2 ≤ B → 0 < n → ∀ d ∈ positive_digits B n, d < B := by
  intro B n HB
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro Hn
    match n, IH, Hn with
    | 0, _, Hn => omega
    | 1, _, _ => simp [positive_digits]; omega
    | m + 2, IH, _ =>
      rw [positive_digits]
      exact double_bound _ _ _ HB (by omega) (IH _ (by omega) (by omega))

theorem double_nonnil : ∀ B ds carry, ds ≠ [] → double B ds carry ≠ [] := by
  intro B ds carry H
  cases ds with
  | nil => exact absurd rfl H
  | cons d tl => simp [double]

theorem positive_digits_nonnil : ∀ B n, 0 < n → positive_digits B n ≠ [] := by
  intro B n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro Hn
    match n, IH, Hn with
    | 0, _, Hn => omega
    | 1, _, _ => simp [positive_digits]
    | m + 2, IH, _ =>
      rw [positive_digits]
      exact double_nonnil _ _ _ (IH _ (by omega) (by omega))

/-- The last digit stays `>= 1`, so the printed decimal carries no leading zero — which Go would read as
    octal. -/
theorem double_last : ∀ B ds carry, 2 ≤ B → carry ≤ 1 →
    (∀ d ∈ ds, d < B) →
    ds ≠ [] → 1 ≤ ds.getLastD 0 →
    1 ≤ (double B ds carry).getLastD 0 := by
  intro B ds
  induction ds with
  | nil => intro carry _ _ _ Hnil _; exact absurd rfl Hnil
  | cons d tl IH =>
    intro carry HB Hc Hall _ Hlast
    rw [List.forall_mem_cons] at Hall
    cases tl with
    | nil =>
      -- d is the last digit; result = (2d+c) mod B :: double [] carry'
      have hd : 1 ≤ d := Hlast
      simp only [double]
      cases hq : (2 * d + carry) / B with
      | zero =>
        -- no carry out: last = (2d+c) mod B = 2d+c >= 2
        have hdm := Nat.div_add_mod (2 * d + carry) B
        rw [hq] at hdm
        simp
        omega
      | succ q => simp  -- carry out: the new last digit is the carry, which is >= 1
    | cons d' tl' =>
      -- the last digit lives in tl
      have Htl : 1 ≤ (double B (d' :: tl') ((2 * d + carry) / B)).getLastD 0 := by
        apply IH _ HB _ Hall.2 (by simp) Hlast
        have : (2 * d + carry) / B < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
        omega
      rw [double]
      cases hdd : double B (d' :: tl') ((2 * d + carry) / B) with
      | nil => exact absurd hdd (double_nonnil _ _ _ (by simp))
      | cons x xs =>
        rw [hdd] at Htl
        simp only [List.getLastD_cons] at Htl ⊢
        exact Htl

theorem positive_digits_last : ∀ B n, 2 ≤ B → 0 < n → 1 ≤ (positive_digits B n).getLastD 0 := by
  intro B n HB
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro Hn
    match n, IH, Hn with
    | 0, _, Hn => omega
    | 1, _, _ => simp [positive_digits]
    | m + 2, IH, _ =>
      rw [positive_digits]
      exact double_last _ _ _ HB (by omega) (positive_digits_bound _ _ HB (by omega))
        (positive_digits_nonnil _ _ (by omega)) (IH _ (by omega) (by omega))

/-- The fold prepends, so the most significant digit ends up first — the printed order. -/
def render (dig : Nat → UInt8) (ds : List Nat) (s : Str) : Str :=
  ds.foldl (fun acc d => dig d :: acc) s

def positive (n : Nat) : Str :=
  render digit (positive_digits 10 n) (str! "")

def integer (z : Int) : Str :=
  match z with
  | .ofNat 0 => str! "0"
  | .ofNat (n + 1) => positive (n + 1)
  | .negSucc n => str! "-" ++ positive (n + 1)

end Fido.Decimal
