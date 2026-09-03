-- Port of the `SFdiv` slice of Rocq 9.2.0's Corelib `Floats/SpecFloat.v` (lean/README.md): definitions only.
import Fido.Prelude

/-! divergences:
  * `positive` is `Nat` (README) with no positivity proof carried: `S754_finite s m e` takes `m : Nat`, so
    `S754_finite s 0 e` is expressible here and not in Rocq.  No ported operation produces it
    (`binary_round_aux` emits `S754_finite` only from a `Zpos` mantissa) and no `Float` statement relies on
    excluding it.
  * `digits2_pos n` is `Nat.log2 n + 1` (kernel-accelerated on literals): the bit length Rocq's structural
    recursion on the positive computes for every `n > 0`; `digits2_pos 0 = 1` has no Rocq counterpart and
    `Zdigits2` keeps Rocq's separate `Z0` arm.
  * `iter_pos f n x` iterates `f` exactly `n` times by structural recursion on the `Nat` count (Rocq iterates
    by the bit structure of the positive; the value `f^n x` is the same) and additionally has
    `iter_pos f 0 x = x`.
  * `Pos.iter xO mx d` and `Z.shiftl m s` (`s > 0`) are `mx * 2 ^ d` and `m * 2 ^ s.toNat`: `Z.pow` takes a `Z`
    exponent and Lean's takes a `Nat`, so each exponent is the `.toNat` of a `Z` that is nonnegative at that arm.
  * `comparison` is `Ordering` (`Eq | Lt | Gt` ↦ `.eq | .lt | .gt`); `Z.compare` is `compare` on `Int`.
  * `Z.div_eucl m' m2` is `(m' / m2, m' % m2)`: Lean's `/` and `%` on `Int` are Euclidean, which is what
    `Z.div_eucl` computes.  Rocq's left-nested triple `(q, e', l)` is Lean's `(q, e', l)` (right-nested).
  * `Section FloatOps`'s `prec emax` are explicit leading arguments of exactly the definitions Rocq generalizes
    over them (`emin`, `fexp`, `shr_fexp`, `binary_round_aux`, `SFdiv_core_binary`, `SFdiv`).
  * The boolean stdlib tests (`Z.eqb`, `Z.leb`, `Z.even`) are `decide` on the corresponding propositions, and
    catch-all `_` match arms are enumerated (see Integer.lean: Lean 4.33 compiles a wildcard arm through a
    `propext`-dependent helper).
-/

namespace Fido.SpecFloat

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive spec_float : Type
  | S754_zero (s : Bool)
  | S754_infinity (s : Bool)
  | S754_nan
  | S754_finite (s : Bool) (m : Nat) (e : Int)
  deriving DecidableEq

export spec_float (S754_zero S754_infinity S754_nan S754_finite)

def emin (prec emax : Int) : Int := 3 - emax - prec
def fexp (prec emax : Int) (e : Int) : Int := max (e - prec) (emin prec emax)

def digits2_pos (n : Nat) : Nat := Nat.log2 n + 1

def Zdigits2 (n : Int) : Int :=
  match n with
  | .ofNat 0 => 0
  | .ofNat (p + 1) => digits2_pos (p + 1)
  | .negSucc p => digits2_pos (p + 1)

def iter_pos {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | n + 1, x => iter_pos f n (f x)

set_option genInjectivity false in
set_option genSizeOfSpec false in
inductive location : Type
  | loc_Exact
  | loc_Inexact (c : Ordering)

export location (loc_Exact loc_Inexact)

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure shr_record : Type where
  Build_shr_record ::
  shr_m : Int
  shr_r : Bool
  shr_s : Bool

export shr_record (Build_shr_record shr_m shr_r shr_s)

def shr_1 (mrs : shr_record) : shr_record :=
  let s := mrs.shr_r || mrs.shr_s
  match mrs.shr_m with
  | .ofNat n => Build_shr_record (.ofNat (n / 2)) (decide (n % 2 = 1)) s
  | .negSucc n => Build_shr_record (-(((n + 1) / 2 : Nat) : Int)) (decide ((n + 1) % 2 = 1)) s

def loc_of_shr_record (mrs : shr_record) : location :=
  match mrs with
  | Build_shr_record _ false false => loc_Exact
  | Build_shr_record _ false true  => loc_Inexact .lt
  | Build_shr_record _ true  false => loc_Inexact .eq
  | Build_shr_record _ true  true  => loc_Inexact .gt

def shr_record_of_loc (m : Int) (l : location) : shr_record :=
  match l with
  | loc_Exact => Build_shr_record m false false
  | loc_Inexact .lt => Build_shr_record m false true
  | loc_Inexact .eq => Build_shr_record m true false
  | loc_Inexact .gt => Build_shr_record m true true

def shr (mrs : shr_record) (e n : Int) : shr_record × Int :=
  match n with
  | .ofNat 0 => (mrs, e)
  | .ofNat (p + 1) => (iter_pos shr_1 (p + 1) mrs, e + n)
  | .negSucc _ => (mrs, e)

def shr_fexp (prec emax : Int) (m e : Int) (l : location) : shr_record × Int :=
  shr (shr_record_of_loc m l) e (fexp prec emax (Zdigits2 m + e) - e)

def round_nearest_even (mx : Int) (lx : location) : Int :=
  match lx with
  | loc_Exact => mx
  | loc_Inexact .lt => mx
  | loc_Inexact .eq => if mx % 2 = 0 then mx else mx + 1
  | loc_Inexact .gt => mx + 1

def binary_round_aux (prec emax : Int) (sx : Bool) (mx ex : Int) (lx : location) : spec_float :=
  let (mrs', e') := shr_fexp prec emax mx ex lx
  let (mrs'', e'') :=
    shr_fexp prec emax (round_nearest_even (shr_m mrs') (loc_of_shr_record mrs')) e' loc_Exact
  match shr_m mrs'' with
  | .ofNat 0 => S754_zero sx
  | .ofNat (m + 1) => if e'' ≤ emax - prec then S754_finite sx (m + 1) e'' else S754_infinity sx
  | .negSucc _ => S754_nan

def shl_align (mx : Nat) (ex ex' : Int) : Nat × Int :=
  match ex' - ex with
  | .negSucc d => (mx * 2 ^ (d + 1), ex')
  | .ofNat _ => (mx, ex)

def cond_Zopp (b : Bool) (m : Int) : Int := if b then -m else m

def new_location_even (nb_steps k : Int) : location :=
  if k = 0 then loc_Exact else loc_Inexact (compare (2 * k) nb_steps)

def new_location_odd (nb_steps k : Int) : location :=
  if k = 0 then loc_Exact
  else loc_Inexact (match compare (2 * k + 1) nb_steps with | .lt => .lt | .eq => .lt | .gt => .gt)

def new_location (nb_steps : Int) : Int → location :=
  if nb_steps % 2 = 0 then new_location_even nb_steps else new_location_odd nb_steps

def SFdiv_core_binary (prec emax : Int) (m1 e1 m2 e2 : Int) : Int × Int × location :=
  let d1 := Zdigits2 m1
  let d2 := Zdigits2 m2
  let e' := min (fexp prec emax (d1 + e1 - (d2 + e2))) (e1 - e2)
  let s := e1 - e2 - e'
  let m' :=
    match s with
    | .ofNat 0 => m1
    | .ofNat (_ + 1) => m1 * 2 ^ s.toNat
    | .negSucc _ => 0
  let q := m' / m2
  let r := m' % m2
  (q, e', new_location m2 r)

def SFdiv (prec emax : Int) (x y : spec_float) : spec_float :=
  match x, y with
  | S754_nan, S754_nan => S754_nan
  | S754_nan, S754_zero _ => S754_nan
  | S754_nan, S754_infinity _ => S754_nan
  | S754_nan, S754_finite _ _ _ => S754_nan
  | S754_zero _, S754_nan => S754_nan
  | S754_infinity _, S754_nan => S754_nan
  | S754_finite _ _ _, S754_nan => S754_nan
  | S754_infinity _, S754_infinity _ => S754_nan
  | S754_infinity sx, S754_finite sy _ _ => S754_infinity (sx ^^ sy)
  | S754_finite sx _ _, S754_infinity sy => S754_zero (sx ^^ sy)
  | S754_infinity sx, S754_zero sy => S754_infinity (sx ^^ sy)
  | S754_zero sx, S754_infinity sy => S754_zero (sx ^^ sy)
  | S754_finite sx _ _, S754_zero sy => S754_infinity (sx ^^ sy)
  | S754_zero sx, S754_finite sy _ _ => S754_zero (sx ^^ sy)
  | S754_zero _, S754_zero _ => S754_nan
  | S754_finite sx mx ex, S754_finite sy my ey =>
    let (mz, ez, lz) := SFdiv_core_binary prec emax mx ex my ey
    binary_round_aux prec emax (sx ^^ sy) mz ez lz

end Fido.SpecFloat
