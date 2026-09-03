-- Port of Integer.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  * `Z.pow` takes a `Z` exponent; Lean core's `Int` power takes a `Nat` exponent, so the `.v`'s
    `2 ^ (bits it - 1)` and `2 ^ (bits it)` are written `2 ^ (bits it - 1).toNat` and `2 ^ (bits it).toNat`.
    Identical on every `Kind` (each exponent is 7, 8, 15, 16, 31, 32, 63 or 64, never negative); the base and
    every surrounding operation stay `Int`.
  * `Z.leb` is written `decide (_ ≤ _)` (`Int.decLe`): Lean core has no separate boolean `Int` comparison.
  * `equalb`'s `| _, _ => false` is enumerated (the 90 off-diagonal pairs).  Lean 4.33 compiles every wildcard
    alternative through a generated `_sparseCasesOn` helper whose proofs depend on `propext`, so the wildcard
    form would put `propext` in the closure of `equalb` and of everything that mentions it; the enumeration
    is the case tree Rocq's own pattern compiler builds from the wildcard, and it keeps the module axiom-free.
  * The constructors `Int`, `Int8`, `Int16`, `Int32`, `Int64` share their spelling with Lean core types, so
    `Kind` is never `open`ed; statements say `Kind.Int` where the `.v` says `Int`.
-/

namespace Fido.Integer

inductive Kind : Type
  | Int | Int8 | Int16 | Int32 | Int64
  | Uint | Uint8 | Uint16 | Uint32 | Uint64
  deriving DecidableEq, Repr

def equalb (a b : Kind) : Bool :=
  match a, b with
  | .Int,  .Int  | .Int8,  .Int8  | .Int16,  .Int16  | .Int32,  .Int32  | .Int64,  .Int64
  | .Uint, .Uint | .Uint8, .Uint8 | .Uint16, .Uint16 | .Uint32, .Uint32 | .Uint64, .Uint64 => true
  | .Int,     .Int8    | .Int,     .Int16   | .Int,     .Int32   | .Int,     .Int64   | .Int,     .Uint
  | .Int,     .Uint8   | .Int,     .Uint16  | .Int,     .Uint32  | .Int,     .Uint64
  | .Int8,    .Int     | .Int8,    .Int16   | .Int8,    .Int32   | .Int8,    .Int64   | .Int8,    .Uint
  | .Int8,    .Uint8   | .Int8,    .Uint16  | .Int8,    .Uint32  | .Int8,    .Uint64
  | .Int16,   .Int     | .Int16,   .Int8    | .Int16,   .Int32   | .Int16,   .Int64   | .Int16,   .Uint
  | .Int16,   .Uint8   | .Int16,   .Uint16  | .Int16,   .Uint32  | .Int16,   .Uint64
  | .Int32,   .Int     | .Int32,   .Int8    | .Int32,   .Int16   | .Int32,   .Int64   | .Int32,   .Uint
  | .Int32,   .Uint8   | .Int32,   .Uint16  | .Int32,   .Uint32  | .Int32,   .Uint64
  | .Int64,   .Int     | .Int64,   .Int8    | .Int64,   .Int16   | .Int64,   .Int32   | .Int64,   .Uint
  | .Int64,   .Uint8   | .Int64,   .Uint16  | .Int64,   .Uint32  | .Int64,   .Uint64
  | .Uint,    .Int     | .Uint,    .Int8    | .Uint,    .Int16   | .Uint,    .Int32   | .Uint,    .Int64
  | .Uint,    .Uint8   | .Uint,    .Uint16  | .Uint,    .Uint32  | .Uint,    .Uint64
  | .Uint8,   .Int     | .Uint8,   .Int8    | .Uint8,   .Int16   | .Uint8,   .Int32   | .Uint8,   .Int64
  | .Uint8,   .Uint    | .Uint8,   .Uint16  | .Uint8,   .Uint32  | .Uint8,   .Uint64
  | .Uint16,  .Int     | .Uint16,  .Int8    | .Uint16,  .Int16   | .Uint16,  .Int32   | .Uint16,  .Int64
  | .Uint16,  .Uint    | .Uint16,  .Uint8   | .Uint16,  .Uint32  | .Uint16,  .Uint64
  | .Uint32,  .Int     | .Uint32,  .Int8    | .Uint32,  .Int16   | .Uint32,  .Int32   | .Uint32,  .Int64
  | .Uint32,  .Uint    | .Uint32,  .Uint8   | .Uint32,  .Uint16  | .Uint32,  .Uint64
  | .Uint64,  .Int     | .Uint64,  .Int8    | .Uint64,  .Int16   | .Uint64,  .Int32   | .Uint64,  .Int64
  | .Uint64,  .Uint    | .Uint64,  .Uint8   | .Uint64,  .Uint16  | .Uint64,  .Uint32  => false

theorem equalb_spec : ∀ a b, equalb a b = true ↔ a = b := by
  intro a b; cases a <;> cases b <;> decide

def signed (it : Kind) : Bool :=
  match it with
  | .Int | .Int8 | .Int16 | .Int32 | .Int64 => true
  | .Uint | .Uint8 | .Uint16 | .Uint32 | .Uint64 => false

/-- Width in bits; `int` and `uint` are 64-bit on the pinned target. -/
def bits (it : Kind) : Int :=
  match it with
  | .Int8  | .Uint8  => 8
  | .Int16 | .Uint16 => 16
  | .Int32 | .Uint32 => 32
  | .Int   | .Int64  | .Uint | .Uint64 => 64

/-- inclusive bounds: signed W is [-2^(W-1), 2^(W-1)-1]; unsigned W is [0, 2^W-1]. -/
def minimum (it : Kind) : Int :=
  if signed it then -(2 ^ (bits it - 1).toNat) else 0

def maximum (it : Kind) : Int :=
  if signed it then 2 ^ (bits it - 1).toNat - 1 else 2 ^ (bits it).toNat - 1

def Representable (it : Kind) (z : Int) : Prop :=
  minimum it ≤ z ∧ z ≤ maximum it

def representableb (it : Kind) (z : Int) : Bool :=
  decide (minimum it ≤ z) && decide (z ≤ maximum it)

-- Rocq: `rewrite andb_true_iff, !Z.leb_le`.  Spelled out by cases on the two `decide`s: `simp` would rewrite
-- under the `↔` through `propext`, and the module stays axiom-free.
theorem representableb_spec :
    ∀ it z, representableb it z = true ↔ Representable it z := by
  intro it z
  change (decide (minimum it ≤ z) && decide (z ≤ maximum it)) = true ↔ minimum it ≤ z ∧ z ≤ maximum it
  cases hm : decide (minimum it ≤ z) <;> cases hM : decide (z ≤ maximum it)
  · exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨h1, _⟩ => absurd h1 (of_decide_eq_false hm)⟩
  · exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨h1, _⟩ => absurd h1 (of_decide_eq_false hm)⟩
  · exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, h2⟩ => absurd h2 (of_decide_eq_false hM)⟩
  · exact ⟨fun _ => ⟨of_decide_eq_true hm, of_decide_eq_true hM⟩, fun _ => rfl⟩

theorem minimum_le_maximum : ∀ it, minimum it ≤ maximum it := by
  intro it; cases it <;> decide

/-- Rocq's `Z.le_refl`.  Core's `Int.le_refl` is proved through `simp` and so depends on `propext`; `a ≤ a`
    unfolds to `Int.NonNeg (a - a)`, and `a - a` reduces to `subNatNat n n` in the two non-zero cases. -/
private theorem le_refl : ∀ a : Int, a ≤ a
  | .ofNat 0 => Int.NonNeg.mk 0
  | .ofNat (n+1) => show Int.NonNeg (Int.subNatNat (n+1) (n+1)) from Int.subNatNat_self _ ▸ Int.NonNeg.mk 0
  | .negSucc n => show Int.NonNeg (Int.subNatNat (n+1) (n+1)) from Int.subNatNat_self _ ▸ Int.NonNeg.mk 0

theorem minimum_representable : ∀ it, Representable it (minimum it) := by
  intro it; exact ⟨le_refl _, minimum_le_maximum it⟩

theorem maximum_representable : ∀ it, Representable it (maximum it) := by
  intro it; exact ⟨minimum_le_maximum it, le_refl _⟩

theorem minimum_pred_not_representable :
    ∀ it, representableb it (minimum it - 1) = false := by
  intro it; cases it <;> decide

theorem maximum_succ_not_representable :
    ∀ it, representableb it (maximum it + 1) = false := by
  intro it; cases it <;> decide

/-- `int` and `int64` are distinct types that share a range only because this target is 64-bit. -/
theorem int_neq_int64 : Kind.Int ≠ Kind.Int64 := nofun

theorem uint_neq_uint64 : Kind.Uint ≠ Kind.Uint64 := nofun

theorem int_range_eq_int64 :
    minimum Kind.Int = minimum Kind.Int64 ∧ maximum Kind.Int = maximum Kind.Int64 := ⟨rfl, rfl⟩

theorem uint_range_eq_uint64 :
    minimum Kind.Uint = minimum Kind.Uint64 ∧ maximum Kind.Uint = maximum Kind.Uint64 := ⟨rfl, rfl⟩

theorem int_bits_64  : bits Kind.Int  = 64 := rfl
theorem uint_bits_64 : bits Kind.Uint = 64 := rfl

end Fido.Integer
