(** The one integer-family and range authority: ten Go integer types over [Z], with [int]/[uint] pinned 64-bit. *)
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

(** Width in bits; [int] and [uint] are 64-bit on the pinned target. *)
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

(** [int] and [int64] are distinct types that share a range only because this target is 64-bit. *)
Lemma int_neq_int64 : Int <> Int64.
Proof. discriminate. Qed.

Lemma uint_neq_uint64 : Uint <> Uint64.
Proof. discriminate. Qed.

Lemma int_range_eq_int64 :
  minimum Int = minimum Int64 /\ maximum Int = maximum Int64.
Proof. split; reflexivity. Qed.

Lemma uint_range_eq_uint64 :
  minimum Uint = minimum Uint64 /\ maximum Uint = maximum Uint64.
Proof. split; reflexivity. Qed.

Lemma int_bits_64  : bits Int  = 64. Proof. reflexivity. Qed.
Lemma uint_bits_64 : bits Uint = 64. Proof. reflexivity. Qed.

Definition platform_minimum  : Z := minimum Int.
Definition platform_maximum  : Z := maximum Int.
Definition platform_unsigned_maximum : Z := maximum Uint.

Lemma platform_minimum_val  : platform_minimum  = -9223372036854775808. Proof. reflexivity. Qed.
Lemma platform_maximum_val  : platform_maximum  =  9223372036854775807. Proof. reflexivity. Qed.
Lemma platform_unsigned_maximum_val : platform_unsigned_maximum = 18446744073709551615. Proof. reflexivity. Qed.
