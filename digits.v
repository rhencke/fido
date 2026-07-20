(** digits.v — the ONE decimal-digit authority (Stdlib-only leaf; consumed by GoRender's
    printer and its all-ASCII proof).  Structural double-and-add over the positive's bits:
    total by the number's own structure, no step budget. *)
From Stdlib Require Import String List Ascii ZArith Lia Bool.
Import ListNotations.
Local Open Scope string_scope.

Definition dec_digit (n : nat) : ascii := ascii_of_nat (48 + n).

(** LSB-first base-[B] digits of a [positive], by STRUCTURAL recursion on its BITS:
    digits(2p) = double(digits p), digits(2p+1) = double + carry — the recursion is the
    positive's own structure, so rendering is total with no step budget of any kind.
    [dds_double] doubles a digit list with an incoming carry (the carry stays <= 1 when
    every digit is < B and B >= 2 — [dds_double_bound]). *)
Fixpoint dds_double (B : nat) (ds : list nat) (carry : nat) : list nat :=
  match ds with
  | nil => match carry with O => nil | _ => carry :: nil end
  | d :: tl => (2 * d + carry) mod B :: dds_double B tl ((2 * d + carry) / B)
  end.
Fixpoint pos_digits (B : nat) (p : positive) : list nat :=
  match p with
  | xH => 1 :: nil
  | xO p' => dds_double B (pos_digits B p') 0
  | xI p' => dds_double B (pos_digits B p') 1
  end.
(** The digit list's VALUE (LSB-first, base [B]) — the semantic anchor of every render proof. *)
Fixpoint dlist_val (B : nat) (ds : list nat) : Z :=
  match ds with
  | nil => 0%Z
  | d :: tl => (Z.of_nat d + Z.of_nat B * dlist_val B tl)%Z
  end.
Lemma dds_double_val : forall B ds carry, (B <> 0)%nat ->
  dlist_val B (dds_double B ds carry) = (2 * dlist_val B ds + Z.of_nat carry)%Z.
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB; cbn [dds_double dlist_val].
  - destruct carry; cbn [dlist_val]; lia.
  - rewrite IH by exact HB.
    pose proof (Nat.div_mod_eq (2 * d + carry) B) as Hdm.
    apply (f_equal Z.of_nat) in Hdm.
    rewrite Nat2Z.inj_add, !Nat2Z.inj_mul in Hdm. nia.
Qed.
Lemma pos_digits_val : forall B p, (B <> 0)%nat -> dlist_val B (pos_digits B p) = Zpos p.
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [pos_digits].
  - rewrite dds_double_val by exact HB. rewrite IH, Pos2Z.inj_xI. lia.
  - rewrite dds_double_val by exact HB. rewrite IH, Pos2Z.inj_xO. lia.
  - cbn [dlist_val]. lia.
Qed.
Lemma dds_double_bound : forall B ds carry, (2 <= B)%nat -> (carry <= 1)%nat ->
  Forall (fun d => (d < B)%nat) ds -> Forall (fun d => (d < B)%nat) (dds_double B ds carry).
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB Hc Hall; cbn [dds_double].
  - destruct carry as [| c']; [ constructor | constructor; [ lia | constructor ] ].
  - inversion Hall; subst. constructor.
    + apply Nat.mod_upper_bound; lia.
    + apply IH; [ lia | | assumption ].
      assert ((2 * d + carry) / B < 2)%nat by (apply Nat.Div0.div_lt_upper_bound; lia). lia.
Qed.
Lemma pos_digits_bound : forall B p, (2 <= B)%nat ->
  Forall (fun d => (d < B)%nat) (pos_digits B p).
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [pos_digits];
    [ apply dds_double_bound; [ lia | lia | exact IH ]
    | apply dds_double_bound; [ lia | lia | exact IH ]
    | constructor; [ lia | constructor ] ].
Qed.
Lemma dds_double_nonnil : forall B ds carry, ds <> nil -> dds_double B ds carry <> nil.
Proof. intros B [| d tl] carry H; [ contradiction | cbn; discriminate ]. Qed.
Lemma pos_digits_nonnil : forall B p, pos_digits B p <> nil.
Proof.
  intros B p; induction p as [p IH | p IH | ]; cbn [pos_digits];
    [ exact (dds_double_nonnil B _ 1 IH) | exact (dds_double_nonnil B _ 0 IH) | discriminate ].
Qed.

(** The MOST significant digit (the LAST of the LSB-first list) is never 0 — so the printed
    decimal has no leading zero (a leading zero would be Go's octal form).  Invariant through
    [dds_double]: doubling keeps the last digit >= 1, or carries out a new last digit 1. *)
Lemma dds_double_last : forall B ds carry, (2 <= B)%nat -> (carry <= 1)%nat ->
  Forall (fun d => (d < B)%nat) ds ->
  ds <> nil -> (1 <= last ds O)%nat ->
  (1 <= last (dds_double B ds carry) O)%nat.
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB Hc Hall Hnil Hlast.
  - contradiction.
  - inversion Hall; subst. cbn [dds_double].
    destruct tl as [| d' tl'].
    + (* d is the last digit; result = (2d+c) mod B :: dds_double [] carry' *)
      cbn [dds_double last] in *.
      destruct ((2 * d + carry) / B) eqn:Hq.
      * (* no carry out: last = (2d+c) mod B = 2d+c >= 2 *)
        cbn [last]. rewrite Nat.mod_small; [ lia | ].
        apply Nat.div_small_iff in Hq; lia.
      * (* carry out: new last digit = the carry, which is 1 *)
        cbn [last]. lia.
    + (* the last digit lives in tl *)
      assert (Htl : (1 <= last (dds_double B (d' :: tl') ((2 * d + carry) / B)) O)%nat).
      { apply IH; [ lia | | assumption | discriminate | ].
        - assert (((2 * d + carry) / B < 2)%nat)
            by (apply Nat.Div0.div_lt_upper_bound; lia). lia.
        - cbn [last] in Hlast. exact Hlast. }
      cbn [last] in *.
      destruct (dds_double B (d' :: tl') ((2 * d + carry) / B)) eqn:Hdd.
      * exfalso. eapply dds_double_nonnil; [ | exact Hdd ]. discriminate.
      * exact Htl.
Qed.
Lemma pos_digits_last : forall B p, (2 <= B)%nat -> (1 <= last (pos_digits B p) O)%nat.
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [pos_digits].
  - apply dds_double_last; [ lia | lia | apply pos_digits_bound; lia
    | apply pos_digits_nonnil | exact IH ].
  - apply dds_double_last; [ lia | lia | apply pos_digits_bound; lia
    | apply pos_digits_nonnil | exact IH ].
  - cbn [last]. lia.
Qed.

(** Render an LSB-first digit list onto a suffix: the fold prepends, so the MOST significant
    digit ends up first — the printed order. *)
Definition render_digits (dig : nat -> ascii) (ds : list nat) (s : string) : string :=
  fold_left (fun acc d => String (dig d) acc) ds s.
Definition print_Z_pos (p : positive) : string :=
  render_digits dec_digit (pos_digits 10 p) "".
Definition print_Z (z : Z) : string :=
  match z with
  | Z0     => "0"
  | Zpos p => print_Z_pos p
  | Zneg p => ("-" ++ print_Z_pos p)%string
  end.
