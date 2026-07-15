(** ============================================================================
    Floats — the ONE float-family descriptor + exact-constant authority.  Two live Go float types, F32 =
    binary32 and F64 = binary64; precision and exponent bound are SINGLE-SOURCED from the one [FloatType]
    descriptor.  The exact untyped floating constant is an exact RATIONAL [FloatConst] (numerator [Z] over a
    [positive] denominator — never a [float], a [spec_float], a decimal source string, or a rounded value).
    Target-directed rounding is a SINGLE direct round of that exact rational at the destination format, over
    [SpecFloat.spec_float] and computable [Z] arithmetic — F32 rounds DIRECTLY at binary32, never through F64
    (the historical double-rounding scar).  Everything here is axiom-free: no [PrimFloat]/[Prim2SF]/[SF2Prim],
    no primitive integers.  No float ARITHMETIC (deferred).
    ============================================================================ *)
From Stdlib Require Import ZArith String.
From Stdlib Require Import Floats.SpecFloat.
Open Scope Z_scope.

(** ---- the one float-type descriptor ---- *)
Inductive FloatType := F32 | F64.

Definition float_type_eqb (a b : FloatType) : bool :=
  match a, b with F32, F32 => true | F64, F64 => true | _, _ => false end.

Lemma float_type_eqb_eq : forall a b, float_type_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Definition float_keyword (ft : FloatType) : string :=
  match ft with F32 => "float32" | F64 => "float64" end%string.

(** binary32 = (prec 24, emax 128); binary64 = (prec 53, emax 1024).  SpecFloat is precision-parameterized,
    so faithful binary32 is the SAME functions with these two magic pairs. *)
Definition float_prec (ft : FloatType) : Z := match ft with F32 => 24 | F64 => 53 end.
Definition float_emax (ft : FloatType) : Z := match ft with F32 => 128 | F64 => 1024 end.

Lemma float_keyword_F32 : float_keyword F32 = "float32"%string. Proof. reflexivity. Qed.
Lemma float_keyword_F64 : float_keyword F64 = "float64"%string. Proof. reflexivity. Qed.
Lemma float_prec_F32 : float_prec F32 = 24.   Proof. reflexivity. Qed.
Lemma float_prec_F64 : float_prec F64 = 53.   Proof. reflexivity. Qed.
Lemma float_emax_F32 : float_emax F32 = 128.  Proof. reflexivity. Qed.
Lemma float_emax_F64 : float_emax F64 = 1024. Proof. reflexivity. Qed.

(** ---- the exact untyped floating constant: an exact rational ---- *)
Record FloatConst := mkFC { fc_num : Z ; fc_den : positive }.

Definition fc_zero : FloatConst := mkFC 0 1.

(** ---- exact rational -> spec_float, then a single direct round at the destination format ----
    [sf_of_Z] embeds an exact integer as a (deliberately non-canonical) [spec_float] mantissa fed only to
    [SFdiv], which normalizes.  [round_float_sf] performs ONE correctly-rounded division of numerator by
    denominator at the destination precision — so F32 rounds directly at binary32, never through binary64. *)
Definition sf_of_Z (z : Z) : spec_float :=
  match z with
  | Z0     => S754_zero false
  | Zpos p => S754_finite false p 0
  | Zneg p => S754_finite true  p 0
  end.

Definition round_float_sf (ft : FloatType) (a : FloatConst) : spec_float :=
  SFdiv (float_prec ft) (float_emax ft) (sf_of_Z (fc_num a)) (sf_of_Z (Zpos (fc_den a))).

Definition cond_Zopp (s : bool) (m : Z) : Z := if s then Z.opp m else m.

(** the exact integer value of an integer-valued finite/zero [spec_float] (nonnegative binary exponent), if
    it denotes an integer — the map back a float->integer constant conversion and the e2e witness use. *)
Definition sf_to_Z (v : spec_float) : option Z :=
  match v with
  | S754_zero _ => Some 0
  | S754_finite s m e =>
      let n := cond_Zopp s (Zpos m) in
      if Z.leb 0 e then Some (n * 2 ^ e)               (* integer by construction *)
      else let d := 2 ^ (- e) in                       (* dyadic n*2^e; integer iff 2^(-e) | n *)
           if Z.eqb (n mod d) 0 then Some (n / d) else None
  | _ => None
  end.

(** ---- ★§30 double-rounding scar: direct binary32 rounding differs from binary64-then-binary32 ----
    input x = 2305843146652647425 = 2^61 + 2^37 + 1.  Direct binary32 rounds UP (strictly above the midpoint)
    to 2^61 + 2^38 = 2305843284091600896; rounding to binary64 first drops the +1 to the exact midpoint
    2^61 + 2^37, which binary32 then rounds to even DOWN to 2^61 = 2305843009213693952.  Both pinned. *)
Definition scar_x : FloatConst := mkFC 2305843146652647425 1.

Example scar_direct_f32 :
  sf_to_Z (round_float_sf F32 scar_x) = Some 2305843284091600896.
Proof. reflexivity. Qed.

Example scar_double_f32_via_f64 :
  sf_to_Z (SFdiv 24 128 (round_float_sf F64 scar_x) (sf_of_Z 1)) = Some 2305843009213693952.
Proof. reflexivity. Qed.

Example scar_direct_differs_double :
  round_float_sf F32 scar_x <> SFdiv 24 128 (round_float_sf F64 scar_x) (sf_of_Z 1).
Proof. discriminate. Qed.

(** ---- §31 precision boundaries: 2^24+1 rounds to 2^24 at binary32; 2^53+1 rounds to 2^53 at binary64 ---- *)
Example round_f32_2p24_plus1 :
  sf_to_Z (round_float_sf F32 (mkFC 16777217 1)) = Some 16777216.
Proof. reflexivity. Qed.

Example round_f64_2p53_plus1 :
  sf_to_Z (round_float_sf F64 (mkFC 9007199254740993 1)) = Some 9007199254740992.
Proof. reflexivity. Qed.

(** small exact values are unchanged. *)
Example round_f32_exact_small : sf_to_Z (round_float_sf F32 (mkFC 3 1)) = Some 3. Proof. reflexivity. Qed.
Example round_f64_exact_small : sf_to_Z (round_float_sf F64 (mkFC 42 1)) = Some 42. Proof. reflexivity. Qed.
