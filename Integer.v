(** Integer — the ONE integer-family descriptor and range authority.  Project scope is the Go 1 language
    surface on modern 64-bit targets: signed [int] and unsigned [uint] are 64-bit.  There is NO
    TargetConfig and no parameterization by Go point release, GOOS, GOARCH, or word size — that abstraction
    tax is not paid until 32-bit support is deliberately chosen in a future reviewed milestone.  The external
    integration build still pins an actual Go toolchain operationally (Dockerfile/Makefile); that pin is not
    threaded through the theorems.

    [Kind] is the sole integer-family descriptor — TEN live Go integer types.  [int]/[int64] are
    DISTINCT types that happen to share a range only because the current target is pinned 64-bit (likewise
    [uint]/[uint64]); [byte]/[rune] are NOT distinct types here (they are aliases and receive source-name
    support only in a later milestone if syntax needs them).  Width, sign, bounds, and keyword are all
    DERIVED from this one descriptor — never a second numeric-range module, never a per-type record, never a
    duplicated numeric literal that becomes a second authority.  The base is pure [Z]/[ZArith]; no
    [PrimInt63]/[Sint63] primitive-integer axiom is ever imported (this file must stay axiom-free). *)
From Stdlib Require Import ZArith String Bool.
Open Scope Z_scope.

Inductive Kind : Type :=
| Int | Int8 | Int16 | Int32 | Int64
| Uint | Uint8 | Uint16 | Uint32 | Uint64.

Definition equalb (a b : Kind) : bool :=
  match a, b with
  | Int,   Int   | Int8,  Int8  | Int16,  Int16  | Int32,  Int32  | Int64,  Int64
  | Uint,  Uint  | Uint8, Uint8 | Uint16, Uint16 | Uint32, Uint32 | Uint64, Uint64 => true
  | _, _ => false
  end.

Lemma equalb_spec : forall a b, equalb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Definition signed (it : Kind) : bool :=
  match it with
  | Int | Int8 | Int16 | Int32 | Int64 => true
  | Uint | Uint8 | Uint16 | Uint32 | Uint64 => false
  end.

(** width in bits — 8/16/32/64; the platform [int]/[uint] are 64-bit on the pinned target. *)
Definition bits (it : Kind) : Z :=
  match it with
  | Int8  | Uint8  => 8
  | Int16 | Uint16 => 16
  | Int32 | Uint32 => 32
  | Int   | Int64  | Uint | Uint64 => 64
  end.

(** inclusive bounds: signed W is [-2^(W-1), 2^(W-1)-1]; unsigned W is [0, 2^W-1]. *)
Definition minimum (it : Kind) : Z :=
  if signed it then - 2 ^ (bits it - 1) else 0.

Definition maximum (it : Kind) : Z :=
  if signed it then 2 ^ (bits it - 1) - 1 else 2 ^ (bits it) - 1.

(** the single representability decision: a mathematical [Z] fits an integer type iff it is within the
    inclusive range.  [Prop] form + its executable [bool] reflection. *)
Definition Representable (it : Kind) (z : Z) : Prop :=
  minimum it <= z <= maximum it.

Definition representableb (it : Kind) (z : Z) : bool :=
  andb (Z.leb (minimum it) z) (Z.leb z (maximum it)).

Lemma representableb_spec :
  forall it z, representableb it z = true <-> Representable it z.
Proof.
  intros it z. unfold representableb, Representable.
  rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.

(** the endpoints are representable; one past either endpoint is not. *)
Lemma minimum_le_maximum : forall it, minimum it <= maximum it.
Proof. destruct it; vm_compute; discriminate. Qed.

Lemma minimum_representable : forall it, Representable it (minimum it).
Proof.
  intro it. unfold Representable. split.
  - apply Z.le_refl.
  - apply minimum_le_maximum.
Qed.

Lemma maximum_representable : forall it, Representable it (maximum it).
Proof.
  intro it. unfold Representable. split.
  - apply minimum_le_maximum.
  - apply Z.le_refl.
Qed.

Lemma minimum_pred_not_representable :
  forall it, representableb it (minimum it - 1) = false.
Proof. destruct it; vm_compute; reflexivity. Qed.

Lemma maximum_succ_not_representable :
  forall it, representableb it (maximum it + 1) = false.
Proof. destruct it; vm_compute; reflexivity. Qed.

(** [int]/[int64] and [uint]/[uint64] are DISTINCT types despite sharing a range on this target. *)
Lemma Int_neq_Int64 : Int <> Int64.
Proof. discriminate. Qed.

Lemma Uint_neq_Uint64 : Uint <> Uint64.
Proof. discriminate. Qed.

Lemma Int_range_eq_Int64 :
  minimum Int = minimum Int64 /\ maximum Int = maximum Int64.
Proof. split; reflexivity. Qed.

Lemma Uint_range_eq_Uint64 :
  minimum Uint = minimum Uint64 /\ maximum Uint = maximum Uint64.
Proof. split; reflexivity. Qed.

(** the platform types are exactly 64-bit. *)
Lemma Int_bits_64  : bits Int  = 64. Proof. reflexivity. Qed.
Lemma Uint_bits_64 : bits Uint = 64. Proof. reflexivity. Qed.

(** ---- derived legacy names (the default-int and platform-uint bounds), kept ONLY as definitions over the
    generic authority above — never a second source of these numeric literals. ---- *)
Definition platform_minimum  : Z := minimum Int.
Definition platform_maximum  : Z := maximum Int.
Definition platform_unsigned_maximum : Z := maximum Uint.

Lemma platform_minimum_val  : platform_minimum  = -9223372036854775808. Proof. reflexivity. Qed.
Lemma platform_maximum_val  : platform_maximum  =  9223372036854775807. Proof. reflexivity. Qed.
Lemma platform_unsigned_maximum_val : platform_unsigned_maximum = 18446744073709551615. Proof. reflexivity. Qed.
