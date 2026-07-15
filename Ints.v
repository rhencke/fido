(** ============================================================================
    Ints — the ONE integer-family descriptor and range authority.  Project scope is the Go 1 language
    surface on modern 64-bit targets: signed [int] and unsigned [uint] are 64-bit.  There is NO
    TargetConfig and no parameterization by Go point release, GOOS, GOARCH, or word size — that abstraction
    tax is not paid until 32-bit support is deliberately chosen in a future reviewed milestone.  The external
    integration build still pins an actual Go toolchain operationally (Dockerfile/Makefile); that pin is not
    threaded through the theorems.

    [IntegerType] is the sole integer-family descriptor — TEN live Go integer types.  [int]/[int64] are
    DISTINCT types that happen to share a range only because the current target is pinned 64-bit (likewise
    [uint]/[uint64]); [byte]/[rune] are NOT distinct types here (they are aliases and receive source-name
    support only in a later milestone if syntax needs them).  Width, sign, bounds, and keyword are all
    DERIVED from this one descriptor — never a second numeric-range module, never a per-type record, never a
    duplicated numeric literal that becomes a second authority.  The base is pure [Z]/[ZArith]; no
    [PrimInt63]/[Sint63] primitive-integer axiom is ever imported (this file must stay axiom-free).
    ============================================================================ *)
From Stdlib Require Import ZArith String Bool.
Open Scope Z_scope.

Inductive IntegerType : Type :=
| IInt | IInt8 | IInt16 | IInt32 | IInt64
| IUint | IUint8 | IUint16 | IUint32 | IUint64.

Definition integer_type_eqb (a b : IntegerType) : bool :=
  match a, b with
  | IInt,   IInt   | IInt8,  IInt8  | IInt16,  IInt16  | IInt32,  IInt32  | IInt64,  IInt64
  | IUint,  IUint  | IUint8, IUint8 | IUint16, IUint16 | IUint32, IUint32 | IUint64, IUint64 => true
  | _, _ => false
  end.

Lemma integer_type_eqb_eq : forall a b, integer_type_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Definition integer_signed (it : IntegerType) : bool :=
  match it with
  | IInt | IInt8 | IInt16 | IInt32 | IInt64 => true
  | IUint | IUint8 | IUint16 | IUint32 | IUint64 => false
  end.

(** width in bits — 8/16/32/64; the platform [int]/[uint] are 64-bit on the pinned target. *)
Definition integer_bits (it : IntegerType) : Z :=
  match it with
  | IInt8  | IUint8  => 8
  | IInt16 | IUint16 => 16
  | IInt32 | IUint32 => 32
  | IInt   | IInt64  | IUint | IUint64 => 64
  end.

(** inclusive bounds: signed W is [-2^(W-1), 2^(W-1)-1]; unsigned W is [0, 2^W-1]. *)
Definition integer_min (it : IntegerType) : Z :=
  if integer_signed it then - 2 ^ (integer_bits it - 1) else 0.

Definition integer_max (it : IntegerType) : Z :=
  if integer_signed it then 2 ^ (integer_bits it - 1) - 1 else 2 ^ (integer_bits it) - 1.

Definition integer_keyword (it : IntegerType) : string :=
  match it with
  | IInt   => "int"    | IInt8  => "int8"  | IInt16  => "int16"  | IInt32  => "int32"  | IInt64  => "int64"
  | IUint  => "uint"   | IUint8 => "uint8" | IUint16 => "uint16" | IUint32 => "uint32" | IUint64 => "uint64"
  end%string.

(** the single representability decision: a mathematical [Z] fits an integer type iff it is within the
    inclusive range.  [Prop] form + its executable [bool] reflection. *)
Definition IntRepresentable (it : IntegerType) (z : Z) : Prop :=
  integer_min it <= z <= integer_max it.

Definition integer_representableb (it : IntegerType) (z : Z) : bool :=
  andb (Z.leb (integer_min it) z) (Z.leb z (integer_max it)).

Lemma integer_representableb_spec :
  forall it z, integer_representableb it z = true <-> IntRepresentable it z.
Proof.
  intros it z. unfold integer_representableb, IntRepresentable.
  rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.

(** the endpoints are representable; one past either endpoint is not. *)
Lemma integer_min_le_max : forall it, integer_min it <= integer_max it.
Proof. destruct it; vm_compute; discriminate. Qed.

Lemma integer_min_representable : forall it, IntRepresentable it (integer_min it).
Proof.
  intro it. unfold IntRepresentable. split.
  - apply Z.le_refl.
  - apply integer_min_le_max.
Qed.

Lemma integer_max_representable : forall it, IntRepresentable it (integer_max it).
Proof.
  intro it. unfold IntRepresentable. split.
  - apply integer_min_le_max.
  - apply Z.le_refl.
Qed.

Lemma integer_min_pred_not_representable :
  forall it, integer_representableb it (integer_min it - 1) = false.
Proof. destruct it; vm_compute; reflexivity. Qed.

Lemma integer_max_succ_not_representable :
  forall it, integer_representableb it (integer_max it + 1) = false.
Proof. destruct it; vm_compute; reflexivity. Qed.

(** the keyword authority is exact for every constructor and injective. *)
Lemma integer_keyword_exact :
  integer_keyword IInt    = "int"%string    /\ integer_keyword IInt8  = "int8"%string  /\
  integer_keyword IInt16  = "int16"%string  /\ integer_keyword IInt32 = "int32"%string /\
  integer_keyword IInt64  = "int64"%string  /\ integer_keyword IUint  = "uint"%string  /\
  integer_keyword IUint8  = "uint8"%string  /\ integer_keyword IUint16 = "uint16"%string /\
  integer_keyword IUint32 = "uint32"%string /\ integer_keyword IUint64 = "uint64"%string.
Proof. repeat split. Qed.

Lemma integer_keyword_inj : forall a b, integer_keyword a = integer_keyword b -> a = b.
Proof. intros [] []; simpl; congruence. Qed.

(** [int]/[int64] and [uint]/[uint64] are DISTINCT types despite sharing a range on this target. *)
Lemma IInt_neq_IInt64 : IInt <> IInt64.
Proof. discriminate. Qed.

Lemma IUint_neq_IUint64 : IUint <> IUint64.
Proof. discriminate. Qed.

Lemma IInt_range_eq_IInt64 :
  integer_min IInt = integer_min IInt64 /\ integer_max IInt = integer_max IInt64.
Proof. split; reflexivity. Qed.

Lemma IUint_range_eq_IUint64 :
  integer_min IUint = integer_min IUint64 /\ integer_max IUint = integer_max IUint64.
Proof. split; reflexivity. Qed.

(** the platform types are exactly 64-bit. *)
Lemma IInt_bits_64  : integer_bits IInt  = 64. Proof. reflexivity. Qed.
Lemma IUint_bits_64 : integer_bits IUint = 64. Proof. reflexivity. Qed.

(** ---- derived legacy names (the default-int and platform-uint bounds), kept ONLY as definitions over the
    generic authority above — never a second source of these numeric literals. ---- *)
Definition int_min  : Z := integer_min IInt.
Definition int_max  : Z := integer_max IInt.
Definition uint_max : Z := integer_max IUint.

Lemma int_min_val  : int_min  = -9223372036854775808. Proof. reflexivity. Qed.
Lemma int_max_val  : int_max  =  9223372036854775807. Proof. reflexivity. Qed.
Lemma uint_max_val : uint_max = 18446744073709551615. Proof. reflexivity. Qed.
