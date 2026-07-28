(* The one decimal-digit authority: double-and-add over a positive's own bits. *)
From Stdlib Require Import String List Ascii ZArith Lia Bool.
Import ListNotations.
Local Open Scope string_scope.

Definition digit (n : nat) : ascii := ascii_of_nat (48 + n).

Fixpoint double (B : nat) (ds : list nat) (carry : nat) : list nat :=
  match ds with
  | nil => match carry with O => nil | _ => carry :: nil end
  | d :: tl => (2 * d + carry) mod B :: double B tl ((2 * d + carry) / B)
  end.
(* LSB-first base-[B] digits, recursing on the positive's own bits, so this is total with no step budget. *)
Fixpoint positive_digits (B : nat) (p : positive) : list nat :=
  match p with
  | xH => 1 :: nil
  | xO p' => double B (positive_digits B p') 0
  | xI p' => double B (positive_digits B p') 1
  end.
Fixpoint value (B : nat) (ds : list nat) : Z :=
  match ds with
  | nil => 0%Z
  | d :: tl => (Z.of_nat d + Z.of_nat B * value B tl)%Z
  end.
Lemma double_val : forall B ds carry, (B <> 0)%nat ->
  value B (double B ds carry) = (2 * value B ds + Z.of_nat carry)%Z.
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB; cbn [double value].
  - destruct carry; cbn [value]; lia.
  - rewrite IH by exact HB.
    pose proof (Nat.div_mod_eq (2 * d + carry) B) as Hdm.
    apply (f_equal Z.of_nat) in Hdm.
    rewrite Nat2Z.inj_add, !Nat2Z.inj_mul in Hdm. nia.
Qed.
Lemma positive_digits_val : forall B p, (B <> 0)%nat -> value B (positive_digits B p) = Zpos p.
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [positive_digits].
  - rewrite double_val by exact HB. rewrite IH, Pos2Z.inj_xI. lia.
  - rewrite double_val by exact HB. rewrite IH, Pos2Z.inj_xO. lia.
  - cbn [value]. lia.
Qed.
Lemma double_bound : forall B ds carry, (2 <= B)%nat -> (carry <= 1)%nat ->
  Forall (fun d => (d < B)%nat) ds -> Forall (fun d => (d < B)%nat) (double B ds carry).
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB Hc Hall; cbn [double].
  - destruct carry as [| c']; [ constructor | constructor; [ lia | constructor ] ].
  - inversion Hall; subst. constructor.
    + apply Nat.mod_upper_bound; lia.
    + apply IH; [ lia | | assumption ].
      assert ((2 * d + carry) / B < 2)%nat by (apply Nat.Div0.div_lt_upper_bound; lia). lia.
Qed.
Lemma positive_digits_bound : forall B p, (2 <= B)%nat ->
  Forall (fun d => (d < B)%nat) (positive_digits B p).
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [positive_digits];
    [ apply double_bound; [ lia | lia | exact IH ]
    | apply double_bound; [ lia | lia | exact IH ]
    | constructor; [ lia | constructor ] ].
Qed.
Lemma double_nonnil : forall B ds carry, ds <> nil -> double B ds carry <> nil.
Proof. intros B [| d tl] carry H; [ contradiction | cbn; discriminate ]. Qed.
Lemma positive_digits_nonnil : forall B p, positive_digits B p <> nil.
Proof.
  intros B p; induction p as [p IH | p IH | ]; cbn [positive_digits];
    [ exact (double_nonnil B _ 1 IH) | exact (double_nonnil B _ 0 IH) | discriminate ].
Qed.

(* The last digit stays >= 1, so the printed decimal carries no leading zero — which Go would read as octal. *)
Lemma double_last : forall B ds carry, (2 <= B)%nat -> (carry <= 1)%nat ->
  Forall (fun d => (d < B)%nat) ds ->
  ds <> nil -> (1 <= last ds O)%nat ->
  (1 <= last (double B ds carry) O)%nat.
Proof.
  intros B ds; induction ds as [| d tl IH]; intros carry HB Hc Hall Hnil Hlast.
  - contradiction.
  - inversion Hall; subst. cbn [double].
    destruct tl as [| d' tl'].
    + (* d is the last digit; result = (2d+c) mod B :: double [] carry' *)
      cbn [double last] in *.
      destruct ((2 * d + carry) / B) eqn:Hq.
      * (* no carry out: last = (2d+c) mod B = 2d+c >= 2 *)
        cbn [last]. rewrite Nat.mod_small; [ lia | ].
        apply Nat.div_small_iff in Hq; lia.
      * (* carry out: new last digit = the carry, which is 1 *)
        cbn [last]. lia.
    + (* the last digit lives in tl *)
      assert (Htl : (1 <= last (double B (d' :: tl') ((2 * d + carry) / B)) O)%nat).
      { apply IH; [ lia | | assumption | discriminate | ].
        - assert (((2 * d + carry) / B < 2)%nat)
            by (apply Nat.Div0.div_lt_upper_bound; lia). lia.
        - cbn [last] in Hlast. exact Hlast. }
      cbn [last] in *.
      destruct (double B (d' :: tl') ((2 * d + carry) / B)) eqn:Hdd.
      * exfalso. eapply double_nonnil; [ | exact Hdd ]. discriminate.
      * exact Htl.
Qed.
Lemma positive_digits_last : forall B p, (2 <= B)%nat -> (1 <= last (positive_digits B p) O)%nat.
Proof.
  intros B p HB; induction p as [p IH | p IH | ]; cbn [positive_digits].
  - apply double_last; [ lia | lia | apply positive_digits_bound; lia
    | apply positive_digits_nonnil | exact IH ].
  - apply double_last; [ lia | lia | apply positive_digits_bound; lia
    | apply positive_digits_nonnil | exact IH ].
  - cbn [last]. lia.
Qed.

(* The fold prepends, so the most significant digit ends up first — the printed order. *)
Definition render (dig : nat -> ascii) (ds : list nat) (s : string) : string :=
  fold_left (fun acc d => String (dig d) acc) ds s.
Definition positive (p : positive) : string :=
  render digit (positive_digits 10 p) "".
Definition integer (z : Z) : string :=
  match z with
  | Z0     => "0"
  | Zpos p => positive p
  | Zneg p => ("-" ++ positive p)%string
  end.
